import Organdy.Blot
import Organdy.Torrent
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.flexible false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Organdy.Optic
open Function Filter MeasureTheory Finset

open Regis.Head.Brecht YM.Regis.Head NormedSpace ProbabilityTheory
open scoped InnerProductSpace ENNReal
variable {E ι τ:Type} [NormedAddCommGroup E][InnerProductSpace ℝ E]
 [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [Fintype ι] [Fintype τ]

def air (k:ℝ)(A: Ink ι)(x:ι→ℝ):ℂ:= haze (write A) k (read x)

variable (π:ι→τ)
variable {D β ε:ℝ}{u w:ι→E}
lemma rivulet (S:Finset ι)(A:Ink ι)(N:A.Within S)
 (h:∀i∈S,∀j∈S,|D^4*inner ℝ (u i) (w j)-β*bell π j (π i)| ≤ ε/4)
 (p q:Freq ι)(t:write A p≠0)(l:write A q≠0):
  |D^4*inner ℝ (combine u p) (combine w q)-
       β*pair (octave π p) (octave π q)| ≤ ε:=by
 rw [combine_duet, duet_pair, harmonics_mul, harmonics_mul]
 simp only [harmonics,read_sub]
 have x (i:Freq ι)(v:write A i≠0):∀a∈({i.1,i.2.1}:Set ι),a∈ S:=by
     have g:=N _ _ (active v)
     intro a r; simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at r; rcases r with (rfl|rfl) <;> tauto
 exact (harmonics_limit (p:=p) (q:=q) fun i z j y=>h i (x p t _ z) j (x q l _ y)).trans_eq (by ring)

open scoped ComplexConjugate

lemma begins (k:ℝ)(A:Ink ι)(u:ι→E)(x:E):
 air k A (spec u x)= haze (write A) k (spec (combine u) x):=by
 unfold air
 congr 1; symm; funext p
 exact combine_spec u p x

lemma billows (d:τ→ℝ){c k b δ B:ℝ}
 (pos:0<b)(w':0<δ)
 (e:0≤ε)(x:lapse ε (64*b)*c^2≤trophy d b δ/4)
 (pk:0<k)(hB:0≤B)
 (Y:D^8*(due (2*B)/k) ≤ ε)
 (A:Ink ι)(S:Finset ι)(N:A.Within S)
 (R: A.qty ≤ c)
 (W: δ ≤ (A.gilt (d ∘ π)).re)
 (G:∀i,‖u i‖ ≤ B)(H:∀p:Freq ι, ‖combine w p‖=‖combine u p‖)
 (C:b≤β)(T:β≤16*b)
 (P:∀i∈S,∀j∈S,|D^4*inner ℝ (u i) (w j)-β*bell π j (π i)| ≤ ε/4):
 trophy d b δ ≤ D^8 * ∫x,(air k A (spec u x)*conj (air k A (spec w x))).re∂stdGaussian E:=by
 simp_rw [begins]

 refine award pk d pos C w' (by positivity) (by positivity) e x Y _ (octave π)
   ((tally A).trans R) ?_ (fun _=>combine_bound (G _) (G _)) H ?_ (rivulet π S A N P)
 · rwa [seen]
 intro p q
 rw [abs_mul,abs_of_pos (pos.trans_le C)]
 exact (mul_le_mul T (duet_bound ..) (abs_nonneg _) (by positivity)).trans_eq (by ring)
