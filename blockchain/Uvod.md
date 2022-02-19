---
marp: true
---

# BlockChain - Uvodno predavanje 

Stefan Nožinić (stefan@lugons.org)

---
# Osnovni koncepti 



---
# Asimetrična kriptografija 

![](./diagrams/6.png)

---

![bg contain](./diagrams/7.png)



---
# Potpisi i dokaz autentičnosti 


---

![bg contain](./diagrams/8.png)

---
# Append-only log 

Vreme  | Autor | Podaci
-------|-------|------
15616  |A      | ....
28615  |B      | ....
30160  |C      | ....


---
# Transakcija 


Sadrži:

* adresu pošiljaoca
* adresu primaoca
* vreme
* identifikator prethodne transakcije
* dodatne metapodatke u zavisnosti od konkretne implementacije
* podatke (npr, vrednost, kod, ...)
* potpis privatnim ključem pošiljaoca


---
# Ledger

* Transakcijski ledger 
* bilansni ledger


---
# Bilansni ledger

Nalog | Stanje
------|------
A     | $300
B     | $400
C     | $1000


---
Nalog | Stanje
------|------
A     | $0
B     | $400
C     | $1300


---
# Bilasni ledger

* sadrži listu bilansa stanja 

---
# Transakcijski ledger

Pošaljilac | Primalac | Vrednost | Kusur
------|-----------|-------|-------
A     | B        | $100   | $400
B     | C        | $100   | $1000
C     | A        | $100   | $0


---
# P2P mreža 

![](./diagrams/1.png)

---
# Double spending

Pošaljilac | Primalac | Vrednost | Kusur
------|-----------|-------|-------
A     | B        | $100   | $400
A     | B        | $600   | $1000


---
# Konsenzus 

![](./diagrams/2.png)



---
# Byzantine Fault Tolerance

![](./diagrams/3.png)


---
# Sybill attack 


![](./diagrams/4.png)



---
# Blokovi 

![](./diagrams/5.png)

---
# Konsenzus u prisustvu malicioznih procesa

* Proof of work 
* Proof of stake 
* Proof of authority 
* Proof of burn
* ...


---
# Čvorovi u mreži

* full nodes - stores whole blockchain, transactions, and is able to validate all transactions
* pruning nodes - prune some transactions after validation (block created) and aging
* lightweight nodes - store blockchain headers only
* miners - create new blocks and perform proof of work / stake / …
* mining pool operators - full node that uses other miners and redistributes reward
* wallets - creates key pairs, store its transactions, view its transactions, send transactions and receive transactions to itself
* mempool - keeps track of unconfirmed but validated transactions


---
# Coinbase

* zašto bi neko validirao blokove ako može da se osloni na druge čvorove da rade težak posao?

---
![bg contain](./diagrams/9.png)


---
# Pitanja?

