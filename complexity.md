---
marp: true
title: O problemima i njihovoj složenosti
author: Stefan Nožinić
theme: default
---

# O problemima i njihovoj složenosti
## Stefan Nožinić

stefan@petnica.rs

---
# Problemi 


- Problem, uopšteno, predstavlja mapiranje skupa ulaza (skup ulaza) na prostor rešenja.
- Jedan takav ulaz nazivamo: instanca problema.




---
# Problemi odlučivanja


- Problem odlučivanja preslikava instance problema na skup $\{YES, NO\}$

---
# Problemi optimizacije 

- Problem optimizacije je traženje najboljeg rešenja po nekom kriterijumu $f : X \to \mathbb{R}$
- Svaki problem optimizacije se može svesti na problem odlučivanja, kako?

---
"Pronađi najbolji oblik koji minimizuje zapreminu" -> "Da li postoji oblik sa zapreminom manjom od k?"

*k određujemo binarnom pretragom*

**Problemi optimizacije su dakle teži od problema odlučivanja**



---
# Problem verifikacije 

- Instance problema je $(I, S)$ gde su:
  - $I$ - instanca problema čije rešenje verifikujemo
  - $S$ - rešenje za $I$

---
# PATH problemi

Dat je graf $G$, čvorovi $u$ i $v$, i broj $k$. Problem PATH preslikava $(G, u, v, k, P)$ u skup $\{YES, NO\}$ na sledeći način:

- **DA** ako važi sve od sledećeg:  
  - Svi čvorovi u $P$ su čvorovi grafa $G$  
  - Prvi čvor u $P$ je $u$
  - Poslednji čvor u $P$ je $v$  
  - Dužina $P$ je najviše $k$

- **NE** u suprotnom.


---
# Problemi kao jezik 

<!-- samo naslov ovde -->

---
# Šta je jezik?


- Jezik je skup reči
- $L_{S,X} =\{x \in X | S(x) = YES\}$

---
# Da li možemo rešiti sve probleme?

---
# Halting problem 

Da li možemo napraviti program koji odlučuje da li zadati program se završava?


---
# NE! Zašto?

---

Neka je P takav program, šta taj program radi sa ovakvim programom na ulazu?

```
PROGRAM X:

    if P(X) is YES then 
        loop forever
    else
        halt
```

---
# Enkodiranje

$$ f : X \to \{0,1\}^* $$ 


-    $f_1 : \{0, 1\}^* \to \{0, 1\}^*$
-    $f_2 : \{0, 1\}^* \to \{0, 1\}^*$
-   $f_1$ i $f_2$ su izračunljivi u polinomnom vremenu
-   Za svaku instancu problema x:
     $f_1(e_1(x)) = e_2(x) \land f_2(e_2(x)) = e_1(x)$


---
# Složenost izračunavanja 

```

PROGRAM DETECT_PALINDROME:
INPUT string S[1..N] of length N 

    for i from 1 to N do 
        if S[i] != S[N-i+1] then 
            return FALSE 
    return TRUE

```

---
# Redukcije

Redukcija sa problema A na B su dve funkcije:

$$ f : X_A \to X_B $$ 

$$ h : \{YES, NO\} \to \{YES, NO\} $$  

$$ \forall x \in L_A, f(x) \in L_{B} $$ 

$$ \forall x \in \bar{L_A}, f(x) \notin L_{B} $$ 

*Ako postoji redukcija sa problema A na problem B, onda je A bar težak koliko i problem B*



---
# Skup P

Problemi koje možemo rešiti u polinomnom vremenu - postoji algoritam koji rešava dati problem sa složenošću koja je polinom od veličine ulaza.

---
# Skup NP 

Problemi čije ršene možemo proveriti u polinomnom vremenu.

$$ P \subseteq NP $$ 

---
# P = NP?



---
# NP-hard 

Ako je $P \neq NP$ onda je problem NP-hard ako nije u P i ako je bar težak koliko i najteži problem u NP.

Ako neki problem možemo redukovati na poznati NP-hard problem, onda je i dati problem NP-hard.

---
# NP-complete

Problem je u NP i NP-hard je.

---
# Dokazivanje da je neki problem NP-complete 

- Dokažemo da je NP - napravimo polinomni algoritam koji verifikuje tačnost rešenja
- Izaberemo neki problem za koji znamo da je NP-complete
- objasnimo redukciju tog poznatog problema na naš problem 
- dokažemo da je takva redukcija polinomno složena

---
# SAT 

Da li zadata Bulova formula je zadovoljiva?

npr ova jeste:

$$ p \lor (q \land \lnot p) $$ 

Ali ova nije:

$$ (p \land \lnot q \land \lnot p) \lor (p \land \lnot p) $$ 



---
# 3-CNF SAT


$$ (x_1 \lor x_2 \lor \lnot x_3) \land (x_1 \lor x_2 \lor x_3) $$


---
# Problem klike

Klika je potpuno povezan podgraf grafa G. 

**Problem:** Da li G ima kliku?

---

# Verifikacija da je K klika od G

---
Od 3 CNF konstruišemo graf:

- Za svaki literal napravimo čvor u grafu
- Dva čvora su povezana ako ne dele klauzulu i ako ne negiraju jedan drugog. 

Ako je formula zadovoljiva, onda izaberemo TRUE literale u različitim klauzulama. 

Ako je K klika od G, onda čvorovi u njoj mogu dobiti vrednost TRUE jer ne dele klauzulu i 
ne negiraju jedan drugog. 

---
# Hamiltonov put




---
# Rešenja za NP-complete probleme u praksi 

- aproksimirajući algoritmi
- kvantno računarstvo 
- paralelni algoritmi

