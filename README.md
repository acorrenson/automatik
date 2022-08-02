# Automatik

A library of formalized graph and automata based algorithms.

## Goals

Graphs and automata-like objects are fundamental in computer-science. They are used in computability, compilation, logic, and formal verification just to name a few examples.

Reasoning about graphs and automaton is hard. Reasoning formally about them is even harder. Moreover, there are many ways of formalizing graphs and automaton in a proof assistant.
**Automatik** is an experimental library attempting to provide a unified formalization of graphs and automaton that can be used for both theoretical developments but also concrete programs. It provides a tradeoff between abstract definitions (in `Prop`) and concrete algorithms (in `Set`). The main goal is to avoid rewriting 10 times definitions and algorithms that are very similar and to provide a catalogue of verified algorithms ready to be executed.

## Use Cases

**Automatik** is developed with the following use cases in mind:

+ Proof of theoretical results
  + Decidability of logical fragments
  + Decidability of model checking problems
+ Certified verification tools
  + Certified model checkers
  + Certified compilation algorithms
+ Certified Optimization/Planning tools
