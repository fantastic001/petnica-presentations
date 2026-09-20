---
marp: true
title: Slučajni algoritmi
author: Stefan Nožinić
date: 2025
---

# Slučajni algoritmi
Stefan Nožinić <stefan@petnica.rs>



---
# Ljubavne veze....


---

# Model

---
# Algoritam


``` example
RELATIONSHIP_ALGORITHM(candidates)
    current = null
    for i=1 to n
        date candidate i 
        if candidates[i] is better than current then
            breakup with current
            start relationship with candidates[i]
            current = candidates[i]
```

---
# Problem

Koliko je očekivan broj promena/raskida?

---
# Najgori slučaj

---

Svaki sledeći kandidat je bolji od trenutnog:

$$ m = \text{broj raskida} = n-1 = O(n) $$ 

---
# Najbolji scenario 

---
Prvi kandidat je najbolji

$$ m = \text{broj raskida} = 0 $$ 

---
# Očekivani broj raskida 

---


$$ \text{očekivani broj raskida} = \sum_{i=0}^n iP(\text{broj raskida} = i) $$ 


---
# Verovatnoća 

$$ P(\epsilon) = \frac{\text{broj pojavljivanja } \epsilon}{\text{ukupan broj svih događaja}} $$ 
---
# Problem sa ovim pristupom

Jako teško dobijamo 

$$ P(\text{broj raskida} = i) $$

---
# Lakši način

Računamo verovatnoću 

$$ P(\text{kandidat i je bolji od trenutnog}) $$ 

---
# Indikator promenljiva

Neka je $X_i$ promenljiva koja je jednaka 1 ako je i-ti kandidat bolji od trenutnog, 0 u suprotnom. 

$$ \text{broj raskida} = \sum_{i=2}^n X_i $$ 

---
# Očekivana vrednost promenljive 

$$ E(x) = \sum_{s \in S_x}  s P(x = s) $$ 

---
$$ E(X_i) = \sum_{s \in \{0,1\}} s \cdot P(X_i = s)  = P(X_i = 1) $$ 

---
# Očekivanje je linearna funkcija


$$ E(x+y) = E(x) + E(y) $$ 

---

$$ E(\text{broj raskida}) = E(\sum_{i=2}^n X_i) = \sum_{i=2}^n E(X_i) = \sum_{i=2}^n P(X_i = 1) $$ 

---
# E sad...

$$ P(X_2 = 1) = ? $$ 

$$ P(X_3 = 1) = ? $$ 

$$ P(X_i = 1) = ? $$ 


---
$$ P(X_i = 1) = \frac{1}{i} $$ 

---
$$ E(m) = \sum_{i=2}^n \frac{1}{i} = \sum_{i=1}^n \frac{1}{i} - 1 = \ln (n) + O(1) -1 = \ln(n) + O(1)$$ 

---
# Slučajni algoritmi

* Ulaz nam ima neku slučajnu raspodelu
* algoritam može da pozove funkciju `RANDOM(a,b)` koja vraća broj u opsegu od a do b po uniformnoj raspodeli. 


---
# Šta je raspodela

Imamo neku promenljivu x kojoj ne znamo tačnu vrednost ali znamo koje su sve moguće vrednosti koje može da ima i koje su šanse za svaku moguću vrednost. 

* U našem primeru je nama ulaz niz kandidata $a_n$ gde je n veličina niza.
    * Ako svaki element može imati K različitih vrednosti, onda je broj ukupnih ulaza $K^n$ 
    * Verovatnoća $P(a_n = (a_1, ..., a_n)) = P(a_n) = \frac{1}{K^n}$
    * U našem primeru, nas je interesovalo rangiranje, kojih ima $n!$ ako su svi elementi različiti.

---
# qsort 

---
-   input a set of numbers S
-   choose random element y in S
-   by comparing each element of S determine S1 and S2 where S1 are
    numbers smaller than y and S2 = S \\ S1
-   recurse on S1 and S2 and then create sorted array of S1 concatenated
    with {y} and S2


---
# Indikator promenljiva 

Neka je $X_{i,j} = 1$ ako su elementi $S_i$ i $S_j$ poređeni. 

$$ E(\text{broj poređenja}) = E(\sum_{i=1}^n \sum_{j>i}^n X_{i,j}) = \sum_{i=1}^n \sum_{j>i}^n E(X_{i,j}) = \sum_{i=1}^n \sum_{j>i}^n P(X_{i,j} = 1) $$ 

---
$$ P(X_{i,j} = 1) = ? $$ 

---

 $$ p_{i,j} = E(X_{i,j}) = \frac{2}{j-i + 1} $$

$$ E(X) = \sum_{i=1}^n \sum_{j>i}^n p_{i,j} =  \sum_{i=1}^n \sum_{j>i}^n \frac{2}{j-i+1} \le  \sum_{i=1}^n \sum_{k=1}^{n-i+1} \frac{2}{k} \le  2\sum_{i=1}^n \sum_{k=1}^{n-i+1} \frac{1}{k} = 2nH_n = O(n \log n) $$ 

---
# Las Vegas algoritmi


``` example
function LasVegasAlgorithm(input):
    repeat
        // Randomly generate choices or parameters
        randomChoices = GenerateRandomChoices()

        // Run the algorithm with random choices
        result = RunAlgorithm(input, randomChoices)

    until IsResultValid(result)

    return result

```

---
Pristup analizi:

-   odrediti sve slučajne ulaze
-   odrediti sve pozive funkcije RANDOM
-   odrediti raspodelu ulaza (obično se može pretpostaviti uniformna)
-   kreirati indikatorsku promenljivu za svako poređenje slučajnog ulaza sa nečim
-   Izračunati očekivano vreme izvršavanja
    -   petlje koriste linearnost očekivanja jer su indikatorske promenljive nezavisne
    -   očekivanje indikatorske promenljive je verovatnoća dobijanja 1 (uspešno poređenje)
-   Izračunati najgore vreme izvršavanja


---
# Monte Carlo algoritmi


Monte Carlo algoritam je slučajni algoritam čiji rezultat može biti netačan sa određenom (obično malom) verovatnoćom.

---

Pristup analizi:

- odrediti sve slučajne ulaze
- odrediti sve pozive funkcije RANDOM
- odrediti raspodelu ulaza (obično se može pretpostaviti uniformna)
- kreirati indikatorsku promenljivu za svako poređenje slučajnog ulaza sa nečim
- Izračunati verovatnoću ispravnog rešenja
- Izračunati očekivano vreme izvršavanja
    - petlje koriste linearnost očekivanja jer su indikatorske promenljive nezavisne
    - očekivanje indikatorske promenljive je verovatnoća dobijanja 1 (uspešno poređenje)


--- 
# Slučajna promenljiva (recap)

* Ima skup dozvoljenih vrednosti 
* Ima raspodelu

Primeri:

* `RANDOM(a,b)` 
    * Vrednosti od a do b - realni brojevi
    * $P(x) = \frac{1}{b-a}$
* `CHOICE(S)` 
    * Vrednosti is skupa S
    * $P(x) = \frac{1}{|S|}$

---


* Normalna raspodela 
    * promenljiva može biti bilo koji realan broj 
    * $P(x) = \frac{1}{\sigma \sqrt{2\pi}} e^{-\frac{1}{2} (\frac{x-\mu}{\sigma})^2}$ 
    * Merenja u prirodi 
        * greška kod instrumenata je $\epsilon \sim N(0, \sigma)$

---

# Buduća istraživanja

* slučajni algoritmi sa različitim pretpostavkama raspodele ulaza 
* _Closed-form_ izrazi za neke probleme

