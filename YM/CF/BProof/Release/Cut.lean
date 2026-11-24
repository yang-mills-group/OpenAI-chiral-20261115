import YM.CF.BProof.Release.Income

/-! Eq (Heavy), pointwise equality of weights after v conditioning. Use U exactly
at draw; holds even when Mark tests not accepted (some estimates below require Evap & Firm).
Define cut = additive log per sector, to be split into exceptional and NPL parts. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BProof.Release
open Function Filter RG Wilson Lattice Finset Work Micro MeasureTheory Mag Angular Angular.Yard Charge Charge.Form Matrix Gauss Roll Precision Locale hot Law
open scoped Topology BigOperators Classical ENNReal Matrix MatrixOrder InnerProductSpace Matrix.Norms.L2Operator
local notation "G"=> SU.group
variable (K:Chart G)(P: Pub G)
variable {s:Side}(Y:Yard s)(T:PathData G){c:Clip}{M:ℕ}(θ κ:ℝ)(y:ℝ){R q w:ℝ}(X:Beam c R Y.short M y) (H:Room Y M)(u:T.Bounds c w R q)(h:θ∈Set.Icc (1/2) 2)(r:BudgetPoint)(β:ℝ)
variable (a:Book K P Y κ X)(Z: Finset Y.Col)(x:Plan Y)(U:Config G s)(V: House Y)

abbrev γ := Sky.reach Y T θ y X Z V x
theorem cash (e:Set.EqOn U (issue Y (γ Y T θ y X Z x V)) ↑Y.field) (v:bed Y κ y (γ Y T θ y X Z x V)=Z): Y.severe κ y U=Z:= (Y.deserts κ y U e).trans ((province ..).trans v)
include H h u a
lemma holds (e:Set.EqOn U (issue Y (γ Y T θ y X Z x V)) ↑Y.field) (v:bed Y κ y (γ Y T θ y X Z x V)=Z)(p:Fares Y y x): Y.Evap κ y U (hot.tape Y T θ X Z x):=by
 let W := tape Y T θ X Z x; refine ⟨a.k,a.on_plane,?_,?_⟩
 · rintro ⟨b,i⟩ g; rw [cash Y T θ κ y X Z x U V e v] at g; rw [e (Y.inter_mem (b,i)),at_issue,γ]; dsimp only; rw [Sky.open_o _ _ _ _ X b V g]; exact rfl
 rintro ⟨b,i⟩ g; rw [cash Y T θ κ y X Z x U V e v] at g; exact hot.plane K P Y T θ κ X Z x a b (Sky.windows K P Y T θ κ y X H u h a b V v p g) i

-- work doesn't see roof. combine logs for exact equality per draw. Jacob and σ, σP membership all gaps, power. Keeper factors `r_crow` log pointwise (to extract later).
omit h u a
abbrev roof_cost := Y.roof Z (hot.tape Y T θ X Z x)
include H
lemma horizon_cost : work Y M Z c T β (roof_cost Y T θ y X Z x)= work Y M Z c T β (hot.tape Y T θ X Z x) := by
 refine sum_congr rfl (fun l g=>?_); obtain ⟨a,b⟩: Stove Y M l∧ Cave Y M l Z:= (mem_filter.mp g).2; unfold Q; rw [cave_dep Y M l H (roof_cost Y T θ y X Z x) a T (tape Y T θ X Z x) (fun i p=> if_neg (b i.1 p))]

-- scalar log, exact. ν draws. This part is not NPL as it is.
def crowd (b:Y.Col) := strong Y M Z y c r T β U (roof_cost Y T θ y X Z x) b- Real.log (Sky.σ P Y y)
def error := -∑ i∈good Y M Z, Taylor y (Y.roll (roof_cost Y T θ y X Z x)) c r T M U β i

def outcost := -(snow Y M y c r T β)+(Fintype.card Y.Col:ℝ)*Real.log (Sky.σ P Y y)+Real.log (Beam.ζ T θ X ∅).det
def cut := (Beam.bill T θ X Z x+ ∑ b∈ Zᶜ, Sky.light P Y T θ y X Z b x)+Night.logDiff (Beam.ζ T θ X) Z + error Y T θ y X r β Z x U + ∑ b∈Z,crowd P Y T θ y X r β Z x U b
include h u
lemma cancels (p:θ=β*g y^2) :
    (Beam.ζ T θ X Z).det * Sky.scale P Y T θ y X Z x * Real.exp (-big Y c r T M β U)= Real.exp (outcost P Y T θ y X r β)* Real.exp (cut P Y T θ y X r β Z x U) := by
 let g₁:=Sky.σ P Y y; let C:=Real.log g₁; let b:= Beam.drive T θ X Z x; let R:= Real.log (Beam.ζ T θ X Z).det; let v:=∑ b∈ Zᶜ,Sky.light P Y T θ y X Z b x
 have he:0<g₁:= Sky.σ_pos ..; have hP:=Beam.journey T θ X Z H u h x; dsimp only at hP
 have hu : (Beam.ζ T θ X Z).det * Sky.scale P Y T θ y X Z x = Real.exp (R+(Zᶜ.card:ℝ)*C+v+ (∑ i∈Zᶜ,Gauss.fans Y (lowerMap Y x) i)/2) := by
   unfold Sky.scale Sky.watch; change _*(g₁^_* Real.exp _) =_; rw [sum_add_distrib, Real.exp_add, Real.exp_add (x:=R+_*C+v),Real.exp_add (x:=R+_*C), Real.exp_add R,Real.exp_log (Beam.bright T θ X Z H u h)]; have hx:g₁^Zᶜ.card=Real.exp ((Zᶜ.card:ℝ)*C):=(by rw [Real.exp_nat_mul,Real.exp_log he])
   simp_rw [←hx,mul_assoc,Sky.inflate, hot.depth,sum_div]; rfl
 rw [hu, ← Real.exp_add, ← Real.exp_add]; congr 1; rw [split_cost Y M Z y c r T β U (roof_cost Y T θ y X Z x), horizon_cost Y T θ y X H β Z x, tape, Beam.turn (p:=p)]; -- tune order
 have ht : (Fintype.card Y.Col : ℝ)=Z.card+(Zᶜ.card:ℝ):=by exact_mod_cast (Finset.card_add_card_compl Z).symm
 unfold cut crowd outcost error Night.logDiff; rw [sum_sub_distrib,sum_const,nsmul_eq_mul,ht]; dsimp only [v,R,C,g₁]; linarith only [hP]
end YM.CF.BProof.Release
