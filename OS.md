---
marp: true
---

# Operativni sistemi 

Stefan  Nožinić (stefan@lugons.org)

---
# Agenda 

* apstrakcija u računarstvu
* model u diskretnom vremenu
* instrukcijski skup 
* arhitektura računara
* CPU, memorija, Ulazno-iylazni podsistem, prekidi



---
# Apstrakcija u računarstvu 

---
# Model u diskretnom vremenu

---
# Instrukcijski skup

---
# Arhitektura računara

---
# CPU 

---
# Memorija

* SRAM
* DRAM
* eksterni medium

---
# Ulazno izlazni podsistem

* podsistem za komunikaciju sa eksternim uređajima
* na primer, HDD, USB, PCIe, ...

---
# Tipovi registara na CPU
* program counter - holds address of next instruction
* accumuative register - holds result of operation
* memory base register - holds data from memory
* memory address register
* instruction register - holds value of current instruction
* state register - contains various flags (zero, sign (S=1 for negative), carry, overflow)
* stack pointer
* general purpose registers (can fetch/put data from/to acumulator)

---
# Prekidi

* način da se softver obavesti o određenim događajima sa spoljašnje strane

---
# Elementi OS


+ communication with BIOS
+ memory management 
+ filesystem
+ process management
+ commandline 

---
# Procesi

+ process is formed from three parts:
  + activity (active / inactive)
  + image
   + attributes 

---

+ image is consisted of:
  + code
  + stack
  + heap memory 

---
+ attributes: 
  + state
  + priority 
+ typical states of process are: ready, active and waiting 
+ quantum: time available per active proess to do execution before it goes into waiting state 


---
# CPU komponenta

+ daje pristup ostalim delovima sistema ya rukovanje prekidima 


---
# Komponenta ya rukovanje procesima

+ kreiranje procesa
+ ubijanje procesa 

---
# Vi[enitno programiranje

this means that two threads cannot write too the same piece of shared memory 

this is achieved using mutexes 

mutex has lock operation which is atomic  (cannot be interrupted)
if mutex is locked, lock operation blocks until it is unlocked so we can write 

```
  thread1()
  {
	  mutex.lock() // will block if mutex is already locked
	  do_stuff()
	  mutex.unlock()
  }

  thread2()
  {
	  mutex.lock() // will block if mutex is already locked
	  do_stuff()
	  mutex.unlock()
  }
  ```

  ---
  # Atomi;ke 


+ sekcija u programu koja ne mo\e biti prekinuta 


---
# Problem 5 filozofa


+ we have 5 philosophers with 5 forks and every philosopher to eat needs 2 forks  (left and right of him)
+ philosophers take forks one by one (left orr right first and then other one) and waits if fork is busy and does not eat 
+ solution: even ones take left first and odd ones take right first 

---
# Sinhronizacija semaforima


+ we have one road and one semaphore
+ cars can pass through the road one by one on semaphore signal
+ cars cannot pass when semaphore is off
+ car passes when semaphore signals
+ when car passes, semaphore turn off 

---
```
stop()
  {
	  mutex.lock()
	  while(! ready)
	  {
		  conditional_variable.wait(lock)
	  }
	  ready = false
  }

  resume()
  {
	  ready = true
	  conditional_variable.notify_one()
  }
  ```

  ---
  # Tajmer

  

+ timer is special kind of driver which registers interrupt on timer tick and during handling of this interrupt, timer:
    + increases system time
    + checks is current process active above time limit (quantum)
    + increases total time of current process
    + checks if processes in sleep should wake up
    + statistics 


---
# Raspoređivanje procesa


+ schedulng is process of bringing process to active mode and pausing other processes 
+ so scheduler must put active process on hold and activate anoother one from list of ready processeswith highest prioority 

---
# Upravljački programi



+ exposes driver interface 
+ for each class of I/O devices this module exposes special driver interface such that drivers can be implemented 
+ this module for every class of I/O device creates abstraction 


---
# HDD - organizacija


+ control unit:
    + control logic
    + address register
    + data register
    + status register
    + time management system 
+ data storage unit:
    + address mechanism
    + memory medium
    + impulse circuits
    + output amplifiers 

---

+ address space is based on cylindrical coordinates (p, phi, z)
+ track is circle for given radius on given height 
+ cylinder is set of all tracks on different heights for given radius 
+ sector is part of circle 
+ between every two sectors there is inter-sector zone 
+ so every sector can be addressed as (u,c,t,s) where u is number of device, c is cylinder, t is track and s is sector number 

---

+ sector capacity is K and is usually K = 512B 
+ cpacity of whole disk: KSTC 
+ sector has header, control tail (ECC, CRC) and data segments 

---

+ for transfer, we use I/O subsystem 
+ in I/O subsystem we can only transfer blocks, block is constant number of successive sectors on one trace 
+ transfer:
    + transfer block to RAM (system zone)
    + activate I/O subsystem
    + wait for transfer to finish 

---

+ also it works vice versa for read
+ I/O subsystem has its bandwidth which depends of data line width and its clock rate 
+ so CPU sends to disk controller:
    + R/W
    + address in RAM
    + adress on disk
    + length in blocks 


---
# Primer čitanja u x86 asm

```
  DAPACK:
          db      0x10
          db      0
  blkcnt: dw      16              ; read 16 blocks, int 13 resets this to # of blocks actually read/written
  db_add: dw      0x7C00          ; memory buffer destination address (0:7c00)
          dw      0               ; in memory page zero
  d_lba:  dd      1               ; put the lba to read in this spot
          dd      0               ; more storage bytes only for big lba's ( > 4 bytes )
   
          mov si, DAPACK          ; address of "disk address packet"
          mov ah, 0x42            ; AL is unused
          mov dl, 0x80            ; drive number 0 (OR the drive # with 0x80)
          int 0x13
          jc short .error
```

---
# Tabele u OS vezane za diskove

---
#  Mount table 

+ contains device description and mount locations
+ contains routines for operating with device

---
#  Allocation table 

per device 

+ contains file names and descriptions
+ index nodes
+ file extension
+ file type (binary or text)
+ version
+ owner, group and permissions
+ size
+ time of creation and modification
+ hidden, system, etc
+ other attributes
+ starting block address or array of addresses of all blocks 

---
#  File descriptor table 

formed per application running in OS 

+ which file name is opened
+ permissions (read / write)
+ current position 

it always has at least 3 files opened: standard input, standarrd output and standard error which are special files 

---
# Table of open files 

one table on whole system 

---
# Memory module 

exposes:

+ memory allocation
+ free(....) functionality 


---
# Memory management 

+ physical address is address on memory while logical address is address of specific process 
+ process can only access through logical space, MMU (memory management unit) translates logical address to physical like this:
    + checks if address is greater than limit and throws exception if yes
    + adds base address to logical address otherwise


---
# Paging 

+ we have pages where every page has its own logical space 
+ first n bits of address represent page while rest represents concrete address oon that page 



---
# Sistem datoteka - filesystem


---
# terminology

+ disk - storage for storing data
+ disk block - minimal amount of data to be read/written
+ block - basic amount of data, always the same or larger than disk block (natural number multiplied by disk block size)
+ volume - logical representation of disk or partition of disk
+ superblock - area where info about volume is stored
+ metadata
+ inode - place for storing metadata (FCB, file record)
+ extent - pair of starting block and length of following block array
+ attribute - pair of key-value such as filename file size etc

---
# file metadata 

+ file name
+ file owner
+ file access permissions
+ file size
+ date of creation
+ date of last read
+ date of last write
+ file type
+ reference to the directory containing the file
+ pointer to data array of a file (or can be list of pointers to the data blocks)

also we can store pointer to list of pointers to blocks or, if we want even larger amount of data per file, we can store pointer to pointers to
pointers to blocks  and this is called double-indirect blocks 

also we can keep list of extents 

---
# Directory 

stores list of file inode pointers as well as pointers to other directories 

it can store names with inode pointers 

contents of a directory can be stores as linear list or tree structure such as:

+ B tree
+ B* tree
+ B+ tree 

contents can be saved as hash tables also 

---
# File system operations 

---
# Initialization 

+ initializes basic empty file system and superblock
+ be careful to store inode of root directory in superblock 
+ this is commonly done by separate program not filesystem driver itself 

---
# Mounting 

+ checking if file system was properly shut down (read indicator in superblock)
+ fixing filesystem if it is dirty
+ builds internal superblock in RAM

---
# Unmounting 

+ flushing out buffered data 
+ modifies superblock is needed

---
# Creating files 

takes directory and file name and creates inode 

---
# creating directories 

takes directory and name and creates inode

it also initializes contents of a directory 

initializes reference to itself and to parent directory 

---
# opening files 

+ takes directory and name and looks up to find inode
+ checks permissions and other stuff
+ returns handle which apps can use to do I/O operations

---
# Writing to files 

+ takes inode (or some kind of handle), position to write, buffer and length of data
+ writes data and modifies metadata 

---
# Reading files 

+ takes inode (or some kind of handle), position, memory buffer and length
+ increments file position with amount of data read
+ maybe modifies metadata? (last read)

---
# Deleting files

+ deletes file from directory
+ waits to oters close file and then deletes inode and (if needed) data contents

---
# Renaming files 

+ takes source directory, source name, destination directory and destination name
+ first lock file system such that others cannot mess up
+ verify if source and destination dirs are same, if they are, simply rename file, otherwise we need to move it
+ check if destination is not child of source, traverse to the root and see if you hit source from destination
+ delete destination name if it refers to a file or empty directory
+ delete source name from source directory
+ create destination name in destination directory
+ change parent to destination directory 

---
# Reading metadata 

+ takes reference to a file
+ returns some inode fields 

---
# write metadata 

similar to reading metadata but modifies fields 

---
# Opening directory 

takes reference to a dir and returns handle 

---
# Reading directory 

takes directory handle and reads contents of a directory and returns something like (name inode) list of pairs 

---
# Extended operations 

+ symbolic links - entries in a directory that refer to another file names
+ hard links - entries that map to same inodes
+ memory mapping of files - map memory buffers to files directly
+ storing key-value attributes
+ indexing - setting keywords to a file and saving this in separate structure to reference files later by keywords
+ journaling/Logging
+ access control lists

---
# Journaling 

main aim is to protect file system from non-consistent writes (e.g. power supply goes off). 

for every write first:

+ we make old content to journal
+ we label journal as registered
+ we write data
+ we label journal as successful

when checking journal, all unregistered ones are made before write so we can delete them and all registered but non successful journals are containing old data which 
is consistent with the file system so we simply get it back to drive where it belongs 


---
# Demoni
+ procesi pokrenuti u pozadini


---
# Zero oor empty process 

process which is running always and is basic infinite loop

---
#  Scheduler for long term 

copies images of processes to/from mass memory if needed 

---
# Identifier or login

communicates with terminal to enable login of users and then calls shell (communicator process) and waits until it exits, after that, enables login again 


---
# Loader and proogram loading 

---
# Introduction 

+ when we compile program into machine code we get object file 
+ we need to load executable into memory and execute pprogram 
+ every object file has starting address zero which is impossible to handle when we have multiuser OS 
+ we need to transform that program into program with new address space provided and calculated by OS 
+ also program can have subprograms and we need to populate addresses with these subprogramsa but they do not need to be in some specific order nor alligned in series 
+ for instance we can have A1B1A2B2 for programs A and B 
+ segment is minimal memory unit where data and program are located 
+ segment can be smaller than program size so we need to allocate multiple segments which do not need to be in series 

---
# Procedura

+ checking permissions and validation
+ filling stack with command line arguments
+ initializing stack pointer and other registers
+ segment allocation
+ loaading program into segments
+ linking - determining values of symbolic references
+ relocation - setting all adress sensitive locations to new address space
+ transferring instructions and data into memory (loading)
+ jumping to start entry and starting execution 

---
# Relocation 

+ loader is responsible to add constant to every relocatable address in program 
+ after coompiling and assembling, program is relocatable 
+ after loading, program in memory is absolute addressed

---
# Compile and start loader 

+ contained in compiler or assembler
+ very simple
+ unnecessary using memory
+ program needs to be always compiled before execution
+ very hard to maintain large number of big segments 

---
# Absolute loader 

+ assembler forms absolutew program
+ neegates nature of assembler
+ mpossible to solve issue when we have multiple subprograms 

---
# BSS loader 

+ more segments for program
+ same segment for data 
+ output of assembler is program and information to which programs (external) is that program dependable

---
# Relocatable loader with direct binding 

+ more segments for data
+ more segments for program

compiler gives:

+ dictionary of external symbols - info on all input and output symbols
+ text table - compiled relocatable code
+ relocatable listing - infoormation of all address-sensitive locations in program


first phase of loading:

+ allocate memory for each segment
+ forming symbol table for global symbols and their absolute addresses 

second phase: 

+ modifying code to relocate its address references tto new addresses 


---
# Dynamic loader 

when we in execution reference global (extern) symbol, it is loaded then and not before that 

---
# Linking strategies 

+ in-segment - for locations in same segment
+ inter-segment - for locations in different segments 


so we need to classify symbols in procedure as local and as global for that procedure 

when we find address sensitive location in code, we fetch: 

+ symbol name to which code references
+ instruction location (offset of segment start)
+ instruction type 

