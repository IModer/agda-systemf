# SystemF as a SOGAT in Agda

This is a *WIP* formalisation/experiment of implementing treesort in SystemF. We define SystemF as a second order generalized algebraic theory.

The inspiration for this paper was from Kaposi Ambrus who told me pure System F is probably enough for all (functional) algorithms. Enough as in its perfectly okay to program in it. The result of this try is the following: Its suprisingly not hard to give treesort. But there are some overheads :

- Church encoding datatypes : while after some practise it is easy to church encode datatypes it is an "unnecessary" thing the programmer has to think about. This can be mitigated by offering a simple syntax for defining them.
- Deriving the iterators and recursors can also be annoying, but this could be automated also.
- The absence of pattern matching also makes things hard, but as far as i know all basic pattern matches can be desugared to iterators/recursors.

This repo is also a plan to implement a System F with the affor mentioned features to see how easier does it get to implement more complex algorithms in that setting. This would incude:

- Parser
- Type checker
- CEK/Krivine machine backend

## Things left to do

### SystemF agda

- Give first order model (CwF style)
- Implement Tree sort :
  - First in plain agda (Done, in Ref-Impl-Sort.agda, but maybe it can be minimized to not need recursor) DONE
  - in SystemF DONE
  - Cleanup DONE

### SystemF haskell

- Implement CEK machine in C or QBE
- Translate the syntax of SystemF into CEK instructions

### Krivine

- Understand reduction on paper
- Give it with debrujn indecies
- Read krivine_agda

## Dependencies

Agda standard library
