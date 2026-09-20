---
marp: true
theme: dark
title: "Kvantno računarstvo"
author: "Stefan Nožinić"
date: "Oktobar 2025"
---

# Klase problema u računarstvu

- Pojmovi: P, NP, NP-težak, NP-kompletan, EXP
- Zašto su ovi pojmovi važni?

---
# Klasa P

- P (Polynomial time) je klasa problema koji se mogu rešiti u polinomijalnom vremenu na determinističkom Turingovom mašinom.
- Primeri problema u P:
  - Sortiranje niza brojeva
  - Pronalaženje najkraćeg puta u grafu (Dijkstra algoritam)
  - Provera da li je broj paran
  - Množenje dva broja
  - Pretraga u sortiranoj listi (binarna pretraga)
  - Računanje najvećeg zajedničkog delioca (GCD) dva broja (Euklidov algoritam)
- Problemi u P su efikasno rešivi na klasičnim računarima.

---
# Klasa NP

- NP (Nondeterministic Polynomial time) je klasa problema za koje se rešenje može verifikovati u polinomijalnom vremenu na determinističkom Turingovom mašinom.
- Primeri problema u NP:
    - Svi problemi iz klase P
    - Problem trgovačkog putnika (TSP)
    - Problem zadovoljavanja Booleove formule (SAT)
    - Problem bojenja grafa
    - Problem faktorizacije velikih brojeva
- NP problemi mogu biti teži za rešavanje nego P problemi, ali ako dobijemo rešenje, možemo ga brzo proveriti.
- Otvoreno pitanje: Da li je P = NP?

---
# NP-težak i NP-kompletan

- NP-težak (NP-hard) su problemi koji su bar toliko teški kao i najteži problemi u NP. Mogu biti i teži od NP problema.
- NP-kompletan (NP-complete) su problemi koji su u NP i NP-težak. Ako se bilo koji NP-kompletan problem može rešiti u polinomijalnom vremenu, onda se svi NP problemi mogu rešiti u polinomijalnom vremenu (P = NP).
- Primeri NP-kompletnih problema:
  - Problem zadovoljavanja Booleove formule (SAT)
  - Problem bojenja grafa
  - Problem trgovačkog putnika (TSP)
- NP-kompletni problemi su ključni za razumevanje granica računarske složenosti.

---
# Klasa EXP

- EXP (Exponential time) je klasa problema koji se mogu rešiti u eksponencijalnom vremenu na determinističkom Turingovom mašinom.
- Primeri problema u EXP:
  - Neki problemi iz oblasti kombinatorike i optimizacije
  - Problemi koji zahtevaju ispitivanje svih mogućih kombinacija
- Problemi u EXP su često nepraktični za rešavanje na velikim ulazima zbog eksponencijalnog rasta vremena rešavanja.
- Veza sa NP: Svi problemi u NP su takođe u EXP, ali nije poznato da li su svi problemi u EXP u NP.

---
# Kvantno računarstvo i klase problema

- Kvantni računari koriste kvantne bitove (kubite) i kvantne fenomene kao što su superpozicija i uplitanje.
- Kvantni algoritmi mogu rešavati određene probleme efikasnije od klasičnih algoritama.
- Primeri kvantnih algoritama:
  - Šorov algoritam za faktorizaciju velikih brojeva (brži od klasičnih metoda)
  - Groverov algoritam za pretragu nestrukturiranih baza podataka


---
# Double Slit Experiment

- Demonstrira dualnost talasa i čestica.
- Pokazuje kako kvantni objekti mogu postojati u superpoziciji stanja.
- Osnova za razumevanje kvantnog računarstva.


---
# Kubiti i superpozicija

- Kubit je osnovna jedinica kvantne informacije.
- Može biti u stanju $|0\rangle$, $|1\rangle$ ili superpoziciji oba stanja.
- Superpozicija omogućava paralelnu obradu informacija.


Konkretno, stanje kubita može biti predstavljeno kao:

$$ |\psi\rangle = \alpha|0\rangle + \beta|1\rangle $$

gde su $\alpha$ i $\beta$ kompleksni brojevi koji zadovoljavaju uslov $|\alpha|^2 + |\beta|^2 = 1$.


Ako izmerimo kubit, verovatnoća da dobijemo stanje $|0\rangle$ je $|\alpha|^2$, a verovatnoća da dobijemo stanje $|1\rangle$ je $|\beta|^2$.

---
# Inherentni paralelizam kvantnog računarstva

- Kvantni računari mogu istovremeno obrađivati veliki broj stanja zahvaljujući superpoziciji.

Na primer, sa n kubita, kvantni računar može biti u superpoziciji $2^n$ različitih stanja istovremeno.

Neka $f: \{0,1\}^n \rightarrow \{0,1\}$ bude funkcija koju želimo da izračunamo za sve moguće ulaze odjednom. Kvantni računar može pripremiti superpoziciju svih mogućih ulaza i evaluirati funkciju $f$ na svim tim ulazima simultano.

---
# Ket notacije

- Ket notacija ($|\psi\rangle$) predstavlja vektore u Hilbertovom prostoru


- Primeri:
  - $|0\rangle$ i $|1\rangle$ su osnovna stanja kubita
  - Superpozicija: $|\psi\rangle = \alpha|0\rangle + \beta|1\rangle$

Takođe, kubit može biti predstavljen kao kolona vektora:

$$ |0\rangle = \begin{pmatrix} 1 \\ 0 \end{pmatrix}, \quad |1\rangle = \begin{pmatrix} 0 \\ 1 \end{pmatrix} $$

Odnosno superpozicija:

$$ |\psi\rangle = \alpha \begin{pmatrix} 1 \\ 0 \end{pmatrix} + \beta \begin{pmatrix} 0 \\ 1 \end{pmatrix} = \begin{pmatrix} \alpha \\ \beta \end{pmatrix} $$

---
# Kvantne logičke operacije

- Kvantne logičke operacije su predstavljene unitarim matricama koje deluju na stanje kubita.


$$ U = \begin{pmatrix} a & b \\ c & d \end{pmatrix} $$

Ili, u ket notaciji:

$$ U|\psi\rangle = U(\alpha|0\rangle + \beta|1\rangle) = \alpha U|0\rangle + \beta U|1\rangle $$

Dakle, dovoljno je da znamo kako operator deluje na osnovna stanja $|0\rangle$ i $|1\rangle$ da bismo odredili njegovo delovanje na bilo koje stanje kubita.

Ono što je ključno jeste da su kvantne logičke operacije reverzibilne, što znači da postoji inverzna operacija koja može vratiti stanje kubita nazad u njegovo originalno stanje.

Dakle, za svaku unitaru matricu $U$, postoji inverzna matrica $U^\dagger$ takva da:

$$ U^\dagger U = U U^\dagger = I $$

Pa samim tim, kvantne logičke operacije ne gube informaciju tokom procesa računanja.

Ovo znači i da svaki operator ima isti broj ulaznih i izlaznih kubitova, što je suprotno od nekih klasičnih logičkih operacija koje mogu biti ireverzibilne (npr. AND, OR).

---
# Kvantna kola

- Kvantna kola su sekvence kvantnih logičkih operacija koje manipulišu stanjem kubita.
- Primeri kvantnih kola:
  - Hadamardovo kolo (H-kolo)
  - CNOT kolo (kontrolisani NOT)
  - Pauli-X, Y, Z operacije 
  - Fazno kolo (Phase gate)
  - Toffoli kolo (kontrolisani kontrolisani NOT)
- Kvantna kola omogućavaju izvođenje kvantnih algoritama.

---
# Primer kvantnog kola u QisKit

```python

import numpy as np
from qiskit import QuantumCircuit

qc = QuantumCircuit(3)
qc.h(0)             
qc.p(np.pi / 2, 0) 
qc.cx(0, 1) 
qc.cx(0, 2) 
print(qc.draw('text'))
```

---
# Hadamardovo kolo

- Hadamardovo kolo (H-kolo) stavlja kubit u superpoziciju stanja $|0\rangle$ i $|1\rangle$.

Matematički, Hadamardova matrica je predstavljena kao:

$$ H = \frac{1}{\sqrt{2}} \begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix} $$

$$ H|0\rangle = \frac{1}{\sqrt{2}}(|0\rangle + |1\rangle) = |+\rangle $$

$$ H|1\rangle = \frac{1}{\sqrt{2}}(|0\rangle - |1\rangle) = |-\rangle $$

