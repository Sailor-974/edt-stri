import re
import io # <-- Nouveau : Pour lire le PDF en mémoire
import requests # <-- Nouveau : Pour télécharger le PDF
from datetime import date, timedelta
import pymupdf

import hashlib
from datetime import datetime
import pytz
from icalendar import Calendar, Event


# On remplace PDF_PATH par l'URL cible
PDF_URL = "https://stri.fr/Gestion_STRI/TAV/L3/EDT_STRI1A_L3IRT_TAV.pdf" # <-- À remplacer par le vrai lien
DEBUG = False
DIAG = False

JOURS = ["Lundi", "Mardi", "Mercredi", "Jeudi", "Vendredi"]
CRENEAUX = [
    ("07h45", "09h45", 7.75),
    ("10h00", "12h00", 10.0),
    ("13h30", "15h30", 13.5),
    ("15h45", "17h45", 15.75),
    ("18h00", "20h00", 18.0),
]
MOIS = {"janv": 1, "jan": 1, "févr": 2, "fév": 2, "fev": 2, "mars": 3, "mar": 3,
        "avr": 4, "mai": 5, "juin": 6, "juil": 7, "août": 8, "aout": 8,
        "sept": 9, "sep": 9, "oct": 10, "nov": 11, "déc": 12, "dec": 12}

RE_SALLE = re.compile(r"^(visio|U\d-\S+|\d[A-Z]-\S+)$", re.IGNORECASE)
RE_HEURE = re.compile(r"^(\d{1,2})h$")
RE_NUM_SEMAINE = re.compile(r"^\d{2}$")
RE_DATE = re.compile(r"^(\d{1,2})/([^\d/\s]+)$")
TOLERANCE_X = 25
DECALAGE_Y = 0

# --- (Garde toutes tes fonctions intermédiaires : lire_spans, classer_couleur, ..., analyser_page inchangées) ---
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

def couleur_en(dessins, point):
    couleur = "BLANC"
    for d in dessins:
        if d.get("fill") is not None and d["rect"].contains(point):
            couleur = classer_couleur(d["fill"])
    return couleur

def interpoler(labels, t):
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

def index_creneau(x0, anchors):
    idx = 0
    for k, a in enumerate(anchors):
        if a <= x0 + TOLERANCE_X:
            idx = k
    return idx

def est_rouge(rgb):
    return rgb is not None and rgb[0] > 0.9 and rgb[1] < 0.15 and rgb[2] < 0.15

def dans_rouge(s, rouges):
    pt = pymupdf.Point((s["x0"] + s["x1"]) / 2, s["y"])
    return any(r.contains(pt) for r in rouges)

def salle_rouge(rouges, x_min, x_max, y_min, y_max):
    for r in rouges:
        cx, cy = (r.x0 + r.x1) / 2, (r.y0 + r.y1) / 2
        if x_min <= cx < x_max and y_min <= cy < y_max:
            return True
    return False

def construire_cellules(spans_ligne, anchors, rouges):
    cellules = []
    for s in sorted(spans_ligne, key=lambda s: s["x0"]):
        if RE_SALLE.match(s["t"]) or dans_rouge(s, rouges):
            if cellules and cellules[-1]["salle"] is None:
                cellules[-1]["salle"] = s["t"]
                cellules[-1]["x_fin"] = s["x1"]
            continue
        idx = index_creneau(s["x0"], anchors)
        if cellules and cellules[-1]["idx"] == idx:
            cellules[-1]["parts"].append(s)
            cellules[-1]["x_fin"] = max(cellules[-1]["x_fin"], s["x1"])
        else:
            cellules.append({"idx": idx, "parts": [s], "salle": None, "x_fin": s["x1"]})
    return cellules

def texte(cell):
    return " ".join(p["t"] for p in cell["parts"])

def separer_prof(brut):
    m = re.match(r"^(.*?)\s*\(([^()]*)\)\s*$", brut)
    if m and m.group(2).strip() not in ("Réseaux", "Télécoms"):
        return m.group(1).strip(), m.group(2).strip()
    return brut.strip(), ""

def annee_pour(mois):
    auj = date.today()
    if mois >= 8 and auj.month < 8:
        return auj.year - 1
    if mois < 8 and auj.month >= 8:
        return auj.year + 1
    return auj.year

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
            if DIAG:
                print(f"⚠ Semaine {e['t']} : structure non reconnue")
            continue

        m = RE_DATE.match(dates[0]["t"])
        mois = MOIS.get(m.group(2).lower().strip("."))
        if mois is None:
            if DIAG:
                print(f"⚠ Semaine {e['t']} : mois inconnu")
            continue
        lundi = date(annee_pour(mois), mois, int(m.group(1)))

        centres = [s["y"] for s in jours]
        pas = (centres[-1] - centres[0]) / 4
        x_grille = max(s["x1"] for s in jours) + 4
        grille = [s for s in bloc if s["x0"] > x_grille]
        anchors = [interpoler(labels, t) for _, _, t in CRENEAUX]

        print(f"\n===== SEMAINE {e['t']} (lundi {lundi.strftime('%d/%m/%Y')}) =====")
        for k, jour in enumerate(JOURS):
            c = centres[k]
            haut, bas, milieu = c - pas / 2, c + pas / 2 , c + DECALAGE_Y
            spans_jour = [s for s in grille if haut <= s["y"] < bas]
            ligne1 = construire_cellules([s for s in spans_jour if s["y"] < milieu], anchors, rouges)
            ligne2 = construire_cellules([s for s in spans_jour if s["y"] >= milieu], anchors, rouges)
            l2 = {c2["idx"]: c2 for c2 in ligne2}
            communs = set()

            print(f"\n[{jour} {(lundi + timedelta(days=k)).strftime('%d/%m')}]")
            for cell in ligne1:
                idx = cell["idx"]
                cell2 = l2.get(idx)
                commun = cell2 is not None and all(p["it"] for p in cell2["parts"])
                p0 = cell["parts"][0]
                couleur = couleur_en(dessins, pymupdf.Point(p0["x0"] + 3, p0["y"]))
                debut, fin, _ = CRENEAUX[idx]

                if commun:
                    communs.add(idx)
                    matiere, prof = texte(cell), texte(cell2)
                    salle = cell2["salle"] or cell["salle"]
                    x_fin = max(cell["x_fin"], cell2["x_fin"])
                else:
                    matiere, prof = separer_prof(texte(cell))
                    salle, x_fin = cell["salle"], cell["x_fin"]

                if couleur in ("VERT_PALE", "GRIS"):
                    if DEBUG:
                        print(f"  REJETÉ ({couleur}) {debut}-{fin} : {texte(cell)}")
                    continue

                prefixe = "CONTRÔLE - " if couleur == "JAUNE" else ""
                if salle and salle.lower() == "visio":
                    salle = "Visio"
                alerte = ""
                if idx + 1 < len(anchors) and x_fin > anchors[idx + 1] + 10:
                    alerte = "  ⚠ la case déborde sur le créneau suivant, à vérifier"

                x_min = anchors[idx] - TOLERANCE_X
                x_max = anchors[idx + 1] - TOLERANCE_X if idx + 1 < len(anchors) else float("inf")
                y_lo, y_hi = (haut, bas) if commun else (haut, milieu)
                a_attribuer = (not salle) and salle_rouge(rouges, x_min, x_max, y_lo, y_hi)
                salle_aff = salle or ("à attribuer" if a_attribuer else "—")

                print(f"  {debut}-{fin} : {prefixe}{matiere} | prof {prof or '—'} | salle {salle_aff}{alerte}")
                resultats.append({"date": lundi + timedelta(days=k), "debut": debut, "fin": fin,
                                  "matiere": matiere, "prof": prof, "salle": salle or "",
                                  "salle_a_attribuer": a_attribuer,
                                  "type": "Contrôle" if couleur == "JAUNE" else "Cours"})

def generer_ics(resultats, nom_fichier="edt-STRI-2026-2027.ics"):
    cal = Calendar()
    cal.add('prodid', '-//EDT STRI Automatique//')
    cal.add('version', '2.0')
    tz = pytz.timezone("Europe/Paris")

    for cours in resultats:
        event = Event()
        
        # Titre : Matière - Salle - Prof
        prefixe = "CONTRÔLE - " if cours["type"] == "Contrôle" else ""
        salle = cours["salle"] if cours["salle"] else ("à attribuer" if cours["salle_a_attribuer"] else "—")
        prof = cours["prof"] if cours["prof"] else "—"
        titre = f"{prefixe}{cours['matiere']} - {salle} - {prof}"
        event.add('summary', titre)
        
        # Conversion des heures "07h45" en objets datetime
        h_deb, m_deb = map(int, cours["debut"].split('h'))
        h_fin, m_fin = map(int, cours["fin"].split('h'))
        
        dt_debut = tz.localize(datetime.combine(cours["date"], datetime.min.time()).replace(hour=h_deb, minute=m_deb))
        dt_fin = tz.localize(datetime.combine(cours["date"], datetime.min.time()).replace(hour=h_fin, minute=m_fin))
        
        event.add('dtstart', dt_debut)
        event.add('dtend', dt_fin)
        
        # Identifiant stable : calculé sur date + heure + matière (ignore la salle pour les mises à jour)
        uid_string = f"{cours['date']}-{cours['debut']}-{cours['matiere']}"
        uid_hash = hashlib.md5(uid_string.encode('utf-8')).hexdigest()
        event.add('uid', f"{uid_hash}@edt-stri")
        
        cal.add_component(event)

    with open(nom_fichier, 'wb') as f:
        f.write(cal.to_ical())
    print(f"Fichier {nom_fichier} généré avec {len(resultats)} événements.")


# --- Modification de la fonction main ---
def main():
    print(f"Téléchargement du PDF depuis : {PDF_URL}...")
    try:
        reponse = requests.get(PDF_URL)
        reponse.raise_for_status() # Lève une erreur si le téléchargement échoue (ex: 404)
        
        # Ouvre le PDF directement depuis les octets téléchargés en mémoire
        pdf_stream = io.BytesIO(reponse.content)
        doc = pymupdf.open(stream=pdf_stream, filetype="pdf")
        
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