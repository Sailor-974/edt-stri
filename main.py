import re
import io
import hashlib
import requests
import pytz
import pymupdf
from datetime import date, datetime, timedelta
from icalendar import Calendar, Event

PDF_URL = "https://stri.fr/Gestion_STRI/TAV/L3/EDT_STRI1A_L3IRT_TAV.pdf"
DEBUG = False     # True : affiche aussi ce qui est rejeté
DIAG = False      # True : affiche tous les textes du PDF avec leurs coordonnées
GROUPE_TP = "TPA"  # ton groupe de TP (None = on garde les TP de tous les groupes)

JOURS = ["Lundi", "Mardi", "Mercredi", "Jeudi", "Vendredi"]

# Horaires possibles (heures décimales). Chaque case est ramenée à la valeur la plus proche.
# Si un nouvel horaire apparaît dans l'EDT, ajoute-le ici.
DEBUTS = [7.75, 9.0, 10.0, 13.5, 15.75, 16.0, 18.0]
FINS = [9.75, 12.0, 15.5, 16.5, 17.75, 18.0, 18.75, 20.0]
# Fin utilisée quand la case n'a ni couleur de fond ni case de salle pour la lire
FIN_PAR_DEFAUT = {7.75: 9.75, 9.0: 12.0, 10.0: 12.0, 13.5: 15.5, 15.75: 17.75, 16.0: 18.0, 18.0: 20.0}

MOIS = {"janv": 1, "jan": 1, "févr": 2, "fév": 2, "fev": 2, "mars": 3, "mar": 3,
        "avr": 4, "mai": 5, "juin": 6, "juil": 7, "août": 8, "aout": 8,
        "sept": 9, "sep": 9, "oct": 10, "nov": 11, "déc": 12, "dec": 12}

RE_SALLE = re.compile(r"^(visio|à venir|a venir|U\d-\S+|\d[A-Z]-\S+)$", re.IGNORECASE)
RE_HEURE = re.compile(r"^(\d{1,2})h$")
RE_NUM_SEMAINE = re.compile(r"^\d{2}$")
RE_DATE = re.compile(r"^(\d{1,2})/([^\d/\s]+)$")
RE_TP = re.compile(r"\s*(?:[-–]\s*)?\(?\bTP[A-Z]\b\)?")
RE_CODE = re.compile(r"^[A-Z]{2,}\d[A-Z0-9]*$")
RE_INITIALES = re.compile(r"[A-Za-z]{2,5}(?: ?& ?[A-Za-z]{2,5})?")   # GR, AnAn, ME & OM...
ECART_MAX = 15      # écart max (points) entre deux textes d'une même case
MARGE_TEXTE = 2     # le texte démarre un peu après le bord gauche de la case
MARGE_ROUGE = 6
DECALAGE_Y = 0


# ------------------------------------------------------------
# Lecture du PDF
# ------------------------------------------------------------
def lire_spans(page):
    spans = []
    for bloc in page.get_text("dict")["blocks"]:
        for ligne in bloc.get("lines", []):
            for s in ligne["spans"]:
                t = re.sub(r"\s+", " ", s["text"]).strip()
                if not t:
                    continue
                x0, y0, x1, y1 = s["bbox"]
                police = s["font"].lower()
                italique = bool(s["flags"] & 2) or "italic" in police or "oblique" in police
                spans.append({"t": t, "x0": x0, "x1": x1, "y": (y0 + y1) / 2, "it": italique})
    return spans


def classer_couleur(rgb):
    if rgb is None:
        return "BLANC"
    r, g, b = rgb
    if r > 0.9 and 0.7 < g < 0.8 and b < 0.1:
        return "ORANGE"
    if r > 0.9 and g > 0.9 and b < 0.1:
        return "JAUNE"
    if 0.5 < r < 0.6 and g > 0.8 and 0.3 < b < 0.4:
        return "VERT_PALE"
    if r > 0.97 and g > 0.97 and b > 0.97:
        return "BLANC"
    if abs(r - g) < 0.05 and abs(g - b) < 0.05 and 0.5 < r < 0.95:
        return "GRIS"
    return "AUTRE"


def fond_en(dessins, point):
    """Couleur et rectangle du fond qui contient le point (le dessin du dessus)."""
    couleur, rect = "BLANC", None
    for d in dessins:
        if d.get("fill") is not None and d["rect"].contains(point):
            couleur, rect = classer_couleur(d["fill"]), d["rect"]
    return couleur, rect


def est_rouge(rgb):
    return rgb is not None and rgb[0] > 0.9 and rgb[1] < 0.15 and rgb[2] < 0.15


def dans_rouge(s, rouges):
    pt = pymupdf.Point((s["x0"] + s["x1"]) / 2, s["y"])
    return any(r.contains(pt) for r in rouges)


def rouge_dans(rouges, x_min, x_max, y_min, y_max):
    for r in rouges:
        cx, cy = (r.x0 + r.x1) / 2, (r.y0 + r.y1) / 2
        if x_min <= cx < x_max and y_min <= cy < y_max:
            return r
    return None


# ------------------------------------------------------------
# Conversion position <-> heure, d'après les étiquettes d'heures de l'en-tête
# ------------------------------------------------------------
def interpoler(labels, t):
    """Position x d'une heure t."""
    if t in labels:
        return labels[t]
    hs = sorted(labels)
    if t < hs[0]:
        a, b = hs[0], hs[1]
    elif t > hs[-1]:
        a, b = hs[-2], hs[-1]
    else:
        a = max(h for h in hs if h < t)
        b = min(h for h in hs if h > t)
    return labels[a] + (t - a) * (labels[b] - labels[a]) / (b - a)


def heure_depuis_x(labels, x):
    """Heure (décimale) correspondant à une position x."""
    hs = sorted(labels)
    if x <= labels[hs[0]]:
        a, b = hs[0], hs[1]
    elif x >= labels[hs[-1]]:
        a, b = hs[-2], hs[-1]
    else:
        a = max(h for h in hs if labels[h] <= x)
        b = hs[hs.index(a) + 1]
    return a + (x - labels[a]) * (b - a) / (labels[b] - labels[a])


def accrocher(t, valeurs):
    return min(valeurs, key=lambda v: abs(v - t))


def fmt(t):
    h = int(t)
    m = round((t - h) * 60)
    return f"{h:02d}h{m:02d}"


def fin_par_defaut(debut, trois_heures):
    """TP et BE/Projets durent 3h ; les autres cours 2h."""
    return accrocher(debut + 3.0, FINS) if trois_heures else FIN_PAR_DEFAUT[debut]


# ------------------------------------------------------------
# Cases, intitulés
# ------------------------------------------------------------
def construire_cellules(spans_ligne, labels, rouges, dessins):
    """Regroupe les textes d'une ligne en cases. La salle est le texte de type salle
    (ou tout texte posé dans une case rouge) qui suit la case sur la même ligne."""
    cellules = []
    for s in sorted(spans_ligne, key=lambda s: s["x0"]):
        if RE_SALLE.match(s["t"]) or dans_rouge(s, rouges):
            if cellules and cellules[-1]["salle"] is None:
                _, rect = fond_en(dessins, pymupdf.Point((s["x0"] + s["x1"]) / 2, s["y"]))
                x_salle = rect.x1 if rect is not None and rect.width < 200 else s["x1"]
                cellules[-1]["salle"] = s["t"]
                cellules[-1]["x_salle"] = x_salle
            continue
        cur = cellules[-1] if cellules else None
        if cur is not None and cur["salle"] is None and s["x0"] - cur["parts"][-1]["x1"] <= ECART_MAX:
            cur["parts"].append(s)
        else:
            t = heure_depuis_x(labels, s["x0"] - MARGE_TEXTE)
            cellules.append({"debut": accrocher(t, DEBUTS), "parts": [s],
                             "salle": None, "x_salle": None})
    return cellules


def texte(cell):
    return " ".join(p["t"] for p in cell["parts"])


def analyser_intitule(brut):
    """Sépare matière, prof, groupe de TP et code projet.
    'Tech. de trans. (TPB) (EG)' -> ('Tech. de trans.', 'EG', 'TPB', '')
    'Res. Entreprise - TPC - TG' -> ('Res. Entreprise', 'TG', 'TPC', '')
    'Phy (Réseaux) (RK)'         -> ('Phy (Réseaux)', 'RK', '', '')
    'Sport ((Rattrapage)'        -> ('Sport (Rattrapage)', '', '', '')"""
    brut = brut.replace("((", "(")
    m = re.search(r"\bTP[A-Z]\b", brut)
    groupe = m.group(0) if m else ""
    txt = RE_TP.sub("", brut).strip(" -–")
    prof, code = "", ""
    m = re.match(r"^(.*?)\s*\(([^()]*)\)\s*$", txt)
    if m:
        contenu = m.group(2).strip()
        if RE_INITIALES.fullmatch(contenu):
            prof, txt = contenu, m.group(1).strip()          # initiales du prof
        elif RE_CODE.match(contenu):
            code, txt = contenu, m.group(1).strip()          # code projet
        # sinon : (Réseaux), (Télécoms), (Rattrapage)... font partie du nom
    else:
        m = re.match(r"^(.*?)\s+[-–]\s+([A-Za-z&. ]{2,8})$", txt)
        if m:
            txt, prof = m.group(1).strip(), m.group(2).strip()
    return txt.strip(), prof, groupe, code


def annee_pour(mois):
    auj = date.today()
    if mois >= 8 and auj.month < 8:
        return auj.year - 1
    if mois < 8 and auj.month >= 8:
        return auj.year + 1
    return auj.year


# ------------------------------------------------------------
# Analyse d'une page
# ------------------------------------------------------------
def analyser_page(page, resultats):
    spans = lire_spans(page)
    dessins = page.get_drawings()
    rouges = [d["rect"] for d in dessins if d.get("fill") is not None and est_rouge(d["fill"])]
    if DIAG:
        for s in sorted(spans, key=lambda s: (round(s["y"]), s["x0"])):
            print(f"y={s['y']:.1f} x0={s['x0']:.1f} x1={s['x1']:.1f} it={int(s['it'])} | {s['t']}")

    entetes = sorted((s for s in spans if RE_NUM_SEMAINE.match(s["t"])), key=lambda s: s["y"])
    for i, e in enumerate(entetes):
        y_min = e["y"] - 15
        y_max = entetes[i + 1]["y"] - 15 if i + 1 < len(entetes) else float("inf")
        bloc = [s for s in spans if y_min <= s["y"] < y_max]

        labels = {int(RE_HEURE.match(s["t"]).group(1)): s["x0"]
                  for s in bloc if RE_HEURE.match(s["t"]) and abs(s["y"] - e["y"]) < 10}
        jours = sorted((s for s in bloc if s["t"] in JOURS), key=lambda s: s["y"])
        dates = sorted((s for s in bloc if RE_DATE.match(s["t"]) and s["x0"] < e["x0"]),
                       key=lambda s: s["y"])
        if len(labels) < 3 or len(jours) != 5 or not dates:
            print(f"⚠ Semaine {e['t']} : structure non reconnue "
                  f"(heures: {len(labels)}, jours: {len(jours)}, date: {len(dates)}). Passe DIAG = True.")
            continue

        m = RE_DATE.match(dates[0]["t"])
        mois = MOIS.get(m.group(2).lower().strip("."))
        if mois is None:
            print(f"⚠ Semaine {e['t']} : mois inconnu dans « {dates[0]['t']} »")
            continue
        lundi = date(annee_pour(mois), mois, int(m.group(1)))

        centres = [s["y"] for s in jours]
        pas = (centres[-1] - centres[0]) / 4
        x_grille = max(s["x1"] for s in jours) + 4
        grille = [s for s in bloc if s["x0"] > x_grille]

        print(f"\n===== SEMAINE {e['t']} (lundi {lundi.strftime('%d/%m/%Y')}) =====")
        for k, jour in enumerate(JOURS):
            c = centres[k]
            haut, bas, milieu = c - pas / 2, c + pas / 2, c + DECALAGE_Y
            spans_jour = [s for s in grille if haut <= s["y"] < bas]
            ligne1 = construire_cellules([s for s in spans_jour if s["y"] < milieu], labels, rouges, dessins)
            ligne2 = construire_cellules([s for s in spans_jour if s["y"] >= milieu], labels, rouges, dessins)
            l2 = {c2["debut"]: c2 for c2 in ligne2}
            communs = set()

            print(f"\n[{jour} {(lundi + timedelta(days=k)).strftime('%d/%m')}]")
            for cell in ligne1:
                p0 = cell["parts"][0]
                couleur, rect = fond_en(dessins, pymupdf.Point(p0["x0"] + 3, p0["y"]))
                colore = rect is not None and couleur in ("ORANGE", "JAUNE")

                # Début : bord gauche de la case colorée, sinon début du texte
                if colore:
                    t_deb = heure_depuis_x(labels, rect.x0 + 1)
                else:
                    t_deb = heure_depuis_x(labels, p0["x0"] - MARGE_TEXTE)
                debut = accrocher(t_deb, DEBUTS)

                if couleur in ("VERT_PALE", "GRIS"):
                    if DEBUG:
                        print(f"  REJETÉ ({couleur}) {fmt(debut)} : {texte(cell)}")
                    continue

                matiere, prof, groupe, code = analyser_intitule(texte(cell))
                trois_h = bool(groupe or code)

                # Case commune : la ligne du bas ne contient que du texte en italique
                cell2 = l2.get(debut)
                commun = cell2 is not None and all(p["it"] for p in cell2["parts"])
                if commun:
                    communs.add(debut)
                    detail = texte(cell2)
                    if RE_INITIALES.fullmatch(detail):
                        prof = detail                                  # initiales du prof
                    else:
                        matiere = f"{matiere} - {detail}"              # ex. « Travail en autonomie »
                    salle = cell2["salle"] or cell["salle"]
                    x_salle = cell2["x_salle"] or cell["x_salle"]
                    y_lo, y_hi = haut, bas
                else:
                    salle, x_salle = cell["salle"], cell["x_salle"]
                    y_lo, y_hi = haut, milieu

                if groupe and GROUPE_TP and groupe != GROUPE_TP:
                    if DEBUG:
                        print(f"  REJETÉ (autre groupe de TP) {fmt(debut)} : {texte(cell)}")
                    continue

                # Salle : « Visio », « à venir », ou case rouge vide = pas encore attribuée
                a_attribuer = False
                if salle and salle.lower().replace("à", "a") == "a venir":
                    salle, a_attribuer = "", True
                elif salle and salle.lower() == "visio":
                    salle = "Visio"
                rouge = None
                if not salle:
                    rouge = rouge_dans(rouges, interpoler(labels, debut) - MARGE_ROUGE,
                                       interpoler(labels, debut + 3.25), y_lo, y_hi)
                    if rouge is not None:
                        a_attribuer = True

                # Fin : bord droit de la case de salle, de la case rouge ou du fond coloré
                if x_salle:
                    x_fin = x_salle
                elif rouge is not None:
                    x_fin = rouge.x1
                else:
                    x_fin = None
                if colore:
                    x_fin = max(rect.x1, x_fin or 0)
                t_fin, fin_estimee = None, False
                if x_fin:
                    t_fin = heure_depuis_x(labels, x_fin)
                    fin = accrocher(t_fin, FINS)
                else:
                    fin, fin_estimee = fin_par_defaut(debut, trois_h), True
                if fin <= debut:
                    fin, fin_estimee = fin_par_defaut(debut, trois_h), True

                notes = []
                if abs(t_deb - debut) > 0.3:
                    notes.append(f"début brut {t_deb:.2f}")
                if t_fin is not None and abs(t_fin - fin) > 0.3:
                    notes.append(f"fin brute {t_fin:.2f}")
                if fin_estimee:
                    notes.append("fin estimée (bloc de 3h)" if trois_h else "fin estimée")
                alerte = ("  ⚠ " + ", ".join(notes)) if notes else ""

                prefixe = "CONTRÔLE - " if couleur == "JAUNE" else ""
                salle_aff = salle or ("à attribuer" if a_attribuer else "—")
                infos = [f"prof {prof or '—'}", f"salle {salle_aff}"]
                if groupe:
                    infos.append(groupe)
                print(f"  {fmt(debut)}-{fmt(fin)} : {prefixe}{matiere} | " + " | ".join(infos) + alerte)

                resultats.append({"date": lundi + timedelta(days=k), "debut": fmt(debut), "fin": fmt(fin),
                                  "matiere": matiere, "prof": prof, "salle": salle or "",
                                  "salle_a_attribuer": a_attribuer, "groupe": groupe, "code": code,
                                  "type": "Contrôle" if couleur == "JAUNE" else "Cours"})

            if DEBUG:
                for cell2 in ligne2:
                    if cell2["debut"] not in communs:
                        print(f"  REJETÉ (ligne 2, G2) {fmt(cell2['debut'])} : {texte(cell2)}")


# ------------------------------------------------------------
# Génération de l'ICS
# ------------------------------------------------------------
def generer_ics(resultats, nom_fichier="edt-STRI-2026-2027.ics"):
    cal = Calendar()
    cal.add("prodid", "-//EDT STRI Automatique//")
    cal.add("version", "2.0")
    cal.add("x-wr-calname", "EDT_UT")
    cal.add("x-wr-timezone", "Europe/Paris")
    tz = pytz.timezone("Europe/Paris")
    maintenant = datetime.now(pytz.utc)

    for cours in resultats:
        event = Event()

        # Titre : Matière - Salle - Prof (les champs vides sont omis)
        prefixe = "CONTRÔLE - " if cours["type"] == "Contrôle" else ""
        parties = [f"{prefixe}{cours['matiere']}"]
        if cours["salle"]:
            parties.append(cours["salle"])
        elif cours["salle_a_attribuer"]:
            parties.append("salle à attribuer")
        if cours["prof"]:
            parties.append(cours["prof"])
        event.add("summary", " - ".join(parties))

        h_deb, m_deb = map(int, cours["debut"].split("h"))
        h_fin, m_fin = map(int, cours["fin"].split("h"))
        jour = datetime.combine(cours["date"], datetime.min.time())
        event.add("dtstart", tz.localize(jour.replace(hour=h_deb, minute=m_deb)))
        event.add("dtend", tz.localize(jour.replace(hour=h_fin, minute=m_fin)))
        event.add("dtstamp", maintenant)
        if cours["salle"]:
            event.add("location", cours["salle"])

        details = []
        if cours["groupe"]:
            details.append(f"Groupe : {cours['groupe']}")
        if cours["code"]:
            details.append(f"Code : {cours['code']}")
        if cours["salle_a_attribuer"]:
            details.append("Salle pas encore attribuée")
        if details:
            event.add("description", "\n".join(details))

        # Identifiant stable : date + heure + matière + groupe (sans la salle, pour les mises à jour)
        uid = hashlib.md5(
            f"{cours['date']}-{cours['debut']}-{cours['matiere']}-{cours['groupe']}".encode("utf-8")
        ).hexdigest()
        event.add("uid", f"{uid}@edt-stri")
        cal.add_component(event)

    with open(nom_fichier, "wb") as f:
        f.write(cal.to_ical())
    print(f"Fichier {nom_fichier} généré avec {len(resultats)} événements.")


def main():
    print(f"Téléchargement du PDF depuis : {PDF_URL}...")
    try:
        reponse = requests.get(PDF_URL, timeout=30)
        reponse.raise_for_status()
        doc = pymupdf.open(stream=io.BytesIO(reponse.content), filetype="pdf")

        resultats = []
        for page in doc:
            analyser_page(page, resultats)

        print(f"\n{len(resultats)} cours retenus au total.")
        generer_ics(resultats)
        return resultats
    except requests.exceptions.RequestException as e:
        print(f"Erreur lors du téléchargement du PDF : {e}")
        return []


if __name__ == "__main__":
    main()