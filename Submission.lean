import Submission.EndStatement
import Submission.ThreeSum.TernaryFinalSolver

/-- Complete deterministic 3SUM bound in the trusted benchmark model. -/
theorem Race.bound :
    EndStatement.ThreeSum.SolvedInTime ((4800699 : Rat) / 2500000) := by
  exact ThreeSum.solvedInTime_4800699_2500000
