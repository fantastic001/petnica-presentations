---
marp: true
---

# Vrednovanje opcija 

Stefan  Nožinić (stefan@lugons.org)

---
# Agenda 

* Pozadina
* Šta su opcije 
* Modeliranje finansijskih tržišta
* Pretpostavke
* Black-Scholes model 

---
# Šta je finansijsko modeliranje?

---
# Zašto procenjujemo vrednost

---
# Šta moramo uzeti u obzir?

---
# Akcije

* Akcije su udeo u kompaniji
* Kako modeliramo vrednost akcije?


---

$$ S = \sum_{t=0}^T \frac{D_t}{(1 + r_t)^t} $$ 

---
# Konstantna dividenda i rizik

$$ S = \frac{D}{r} $$ 

---
# Kada dividenda raste za g u svakoj iteraciji 

$$ S = \frac{D}{r - g} $$ 

---
# Šta su opcije

* Call opcija predstavlja pravo na kupovinu akcija po staroj ceni S(0) u trenutku T
    * T - vreme izvršenja
    * S(0) - cena izvršenja.
* put opcije ima pravo da proda u trenutku T.
* Opcije imaju svoju cenu, V(0)
* Ako cena akcija padne, call opcija je bezvredna.
* Ako cena akcija poraste, call opcija generiše profit u iznosu razlike jer se akcije mogu kupiti i odmah prodati.



---
# Evropske opcije

Call opcija ima vrednost:

$$ P = \max(S(T) - X, 0) $$ 

Put opcija ima vrednost:

$$ P = \max(X - S(T), 0) $$ 

---
# Američke opcije 

* može instrument biti kupljen/prodat u bilo kom trenutku između t1 i t2 

---
# Evropske Call opcije 

Kolika je vrednost opcije u trenutku T=1:

$$ C_1 = \max(S(1) - X, 0) $$ 


Nama treba C0 da utvrdimo vrednost (valuaciju) opcije u trenutnom vremenu. 

---
# Pretpostavke 

* Vrednost akcije se ponaša po Bernulijevoj raspodeli, odnosno

$$ S(1) = uS(0) $$ 

sa verovatnoćom p 

$$ S(1) = dS(0) $$ 

sa verovatnoćom 1-p

$$ 0 \le d \le  1 \le u $$ 

---


Zamislimo da imamo portfolio od nekog broja date akcije i nekog broja od nerizičnih obveznica. 

$$ V_0 = \Delta S(0) + B $$ 


Sada važi da je: 

$$ V_1 = u\Delta S(0) + (1 + r)B $$ 

sa verovatnćom p, odnosno

$$ V_1 = d\Delta S(0) + (1 + r)B $$ 

sa verovatnoćom 1-p.

Ako cena akcije poreaste, onda je vrednost opcije 

$$ C_u = \max(uS(0) - X, 0) $$ 

Ako cena akcije padne, onda je vrednost opcije: 

$$ C_d = \max(dS(0) - X, 0) $$ 

---

Pošto želimo da portfolio izjednačimo sa opcijom onda rešavamo jednačinu:

$$ u\Delta S(0) + (1 + r)B = C_u $$ 

$$ d\Delta S(0) + (1 + r)B = C_d $$ 

---

$$ C_0 = \frac{1}{1+r} (\frac{1+r-d}{u-d} C_u + \frac{u - 1 - r}{u-d}C_d) $$ 

---
# Kakve smo pretpostavke napravili?

* Da li vrednost instrumenta zavisi od istorije kretanja? 
    * Ako da, onda modelujemo Markovljevijim lancima 
* Ako možemo iskoristiti opciju u terminima t1, ..., tn onda 

$$ C_0 = \frac{1}{(1+r)^n} \sum_{k=0}^n {n \choose k} p^k (1-p)^{n-k} \max(0, u^kd^{n-k}S_0 - X) $$ 

$$ p = \frac{1+r-d}{u-d} $$ 


---
# Black Scholes model 

Pretpostavke:

* Risk-free povraćaj je uvek konstantan 
* Cena akcije se menja po lognormalnoj raspodeli odnosno:

$$ \log S $$ 

se menja po normalnoj raspodeli.
* Opcija je evropska call opcija


---
# Black-Scholes jednačina 

$$ \frac{\partial C}{\partial t} + \frac{1}{2} \sigma^2 S^2(t) \frac{\partial^2 C}{\partial S^2} + rS\frac{\partial C}{\partial S} -rC = 0 $$ 

---
# Kako smo došli do ovoga?


---

$$ C(s,t) = e^{-r(T - t)} \int_{-\inf}^\inf \max(S - X, 0)q(S)dS $$ 

---
# Modeliramo ponašanje cene kao ranije, samo sad imamo za svaki interval dt 

---

$$ q(S)dS = \frac{1}{\sqrt{2\pi \sigma^2}}e^{\frac{-(\log S - \mu)^2}{2\sigma^2}} $$ 

---

%% E(q(S)) = e^{\mu + \sigma^2 / 2} $$ 

Mi želimo da nam očekivanje za S bude: 

$$ se^{r(T - t)} $$ 

---

$$ \mu = \log(S_0) + r(T - t) - \frac{\sigma^2}{2} $$ 

---

$$ \sigma^2 = (T - t)\nu^2 $$ 

---

$$ z = \log(S) - \mu $$ 

$$ dz = \frac{1}{S}dS $$ 

---

$$ C(s,t) = e^{-r(T-t)}\int_0^\inf \frac{\max(S - X, 0)}{S} p(t,z) dz $$

---

$$ \frac{\partial C}{\partial t} + \frac{1}{2} \sigma^2 S^2(t) \frac{\partial^2 C}{\partial S^2} + rS\frac{\partial C}{\partial S} -rC = 0 $$ 



---
# Rešenje 

$$ C(0, t) = 0 $$ 
$$ \lim_{S \to \inf} C(S, t) = S-X $$ 
$$ C(S, T) = \max(S(T) - X, 0) $$ 

---

$$ C(S(t), t) = N(u) S(t) - N(d)Xe^{-r(T-t)} $$ 

$$ u = \frac{1}{\nu\sqrt{T-t}}(\log(\frac{S(t)}{X}) + (r + \nu^2 / 2)(T - t)) $$ 

$$ d = u - \nu\sqrt{T - t} $$ 

---
# Numeričko rešavanje

$$ \int_0^\inf f(x)dx = \int_0^1 f(\frac{t}{1 - t})\frac{dt}{(1 - t)^2} $$ 

Sada integral ovakvog tipa možemo rešiti Monte Karlo metodom:

$$ \int_0^1 f(\frac{t}{1 - t})\frac{dt}{(1 - t)^2} = \frac{1}{N} \sum_{i=1}^N f(\frac{t_i}{1 - t_i})\frac{(1 - t_i)^2} $$ 

---
# Zaključak

* Modeliranje nam pomaže da na sistematian način znamo cene instrumenata
* Za modeliranje nam trebaju pretpostavke o tržištu 
* Danas, često nemamo analitička rešenja


