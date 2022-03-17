# Formal Modeling of Hazard Pointers

This repository contains my independent project from CMU's 17624 Advanced Formal Methods course. I use TLA+ to model and perform simple bounded checking of the hazard pointer concurrent data structure primitive.

## Repository Structure
+ report.pdf contains my final report. It describes the research and is a good starting point.
+ simple_lock.tla is a small model of a mutually exclusive lock. I used this to warm up to TLA+ and PlusCal.
+ hazptr.tla is my main project model. It has some limitations that are described in the report.