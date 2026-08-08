import Lax20Proofs.TMToRam.NumericSemantics
import Lax13Proofs.Imp

/-!
Compilation of normalized Turing statements to IMP+. A stack with numeric
index `k` is represented by array `tm_stack_k`; its active contents are the
prefix below scalar `tm_top_k`, in reverse order, so push, peek, and pop are
constant-size IMP+ fragments. Literal finite-control tables become read-only
arrays with fresh names.
-/

namespace Lax20Proofs.TMToRam

open Lax13Proofs.Imp

def stateVar : String := "tm_state"
def labelVar : String := "tm_label"
def tempVar : String := "tm_temp"
def headVar : String := "tm_head"
def indexVar : String := "tm_index"

def stackName (k : ℕ) : String := "tm_stack_" ++ toString k
def topName (k : ℕ) : String := "tm_top_" ++ toString k
def tableName (i : ℕ) : String := "tm_table_" ++ toString i

/-- Result of compiling a numeric statement. `tables` gives the fresh array
names and their initial literal contents; `nextTable` is the next unused id. -/
structure StmtCompilation where
  com : Com
  tables : List (String × List ℕ)
  nextTable : ℕ

def seqs : List Com → Com
  | [] => .skip
  | c :: cs => .seq c (seqs cs)

/-- Read `table[index]` into `target`. -/
def tableRead (name target : String) (index : Expr) : Com :=
  .assign target (.get name index)

/-- Read a stack head using the zero/successor convention, without changing
the top pointer. -/
def readHead (k : ℕ) : Com :=
  .ite (.eq (.var (topName k)) (.lit 0))
    (.assign headVar (.lit 0))
    (seqs [
      .assign tempVar (.sub (.var (topName k)) (.lit 1)),
      .assign headVar (.add (.get (stackName k) (.var tempVar)) (.lit 1))])

/-- Read a stack head and, in the nonempty case, decrement its top pointer. -/
def readHeadAndPop (k : ℕ) : Com :=
  .ite (.eq (.var (topName k)) (.lit 0))
    (.assign headVar (.lit 0))
    (seqs [
      .assign tempVar (.sub (.var (topName k)) (.lit 1)),
      .assign headVar (.add (.get (stackName k) (.var tempVar)) (.lit 1)),
      .assign (topName k) (.var tempVar)])

/-- Compile a normalized statement, allocating table names from `fresh`. -/
def compileNumericStmt : NumericStmt → ℕ → StmtCompilation
  | .push k table next, fresh =>
      let r := compileNumericStmt next (fresh + 1)
      { com := seqs [
          tableRead (tableName fresh) tempVar (.var stateVar),
          .store (stackName k) (.var (topName k)) (.var tempVar),
          .assign (topName k) (.add (.var (topName k)) (.lit 1)),
          r.com]
        tables := (tableName fresh, table) :: r.tables
        nextTable := r.nextTable }
  | .peek k width table next, fresh =>
      let r := compileNumericStmt next (fresh + 1)
      { com := seqs [readHead k,
          .assign indexVar (.add (.mul (.var stateVar) (.lit width)) (.var headVar)),
          tableRead (tableName fresh) stateVar (.var indexVar), r.com]
        tables := (tableName fresh, table) :: r.tables
        nextTable := r.nextTable }
  | .pop k width table next, fresh =>
      let r := compileNumericStmt next (fresh + 1)
      { com := seqs [readHeadAndPop k,
          .assign indexVar (.add (.mul (.var stateVar) (.lit width)) (.var headVar)),
          tableRead (tableName fresh) stateVar (.var indexVar), r.com]
        tables := (tableName fresh, table) :: r.tables
        nextTable := r.nextTable }
  | .load table next, fresh =>
      let r := compileNumericStmt next (fresh + 1)
      { com := .seq (tableRead (tableName fresh) stateVar (.var stateVar)) r.com
        tables := (tableName fresh, table) :: r.tables
        nextTable := r.nextTable }
  | .branch table yes no, fresh =>
      let ry := compileNumericStmt yes (fresh + 1)
      let rn := compileNumericStmt no ry.nextTable
      { com := .seq (tableRead (tableName fresh) tempVar (.var stateVar))
          (.ite (.eq (.var tempVar) (.lit 0)) rn.com ry.com)
        tables := (tableName fresh, table) :: (ry.tables ++ rn.tables)
        nextTable := rn.nextTable }
  | .goto table, fresh =>
      { com := seqs [tableRead (tableName fresh) labelVar (.var stateVar),
          .assign labelVar (.add (.var labelVar) (.lit 1))]
        tables := [(tableName fresh, table)]
        nextTable := fresh + 1 }
  | .halt, fresh =>
      { com := .assign labelVar (.lit 0), tables := [], nextTable := fresh }

end Lax20Proofs.TMToRam
