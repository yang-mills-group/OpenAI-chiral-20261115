import Gingham.Ruff.Muff
set_option autoImplicit false
set_option maxHeartbeats 500000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Finset Fock Scree Pastry
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator
attribute [local instance] opCStarAlgebra
open Lattice Wilson Laurent Cube SU Lat Spire Scroll Peaks Drapes Rush Precision Tulip Jet
    Tap Laic Dial Paige Vault Pec Skye Branch
variable {N:Side}
open Nacre Plumes

variable {f g:Chin N→OP N}{a c e:ℝ} (h:Plumes f g a c e)
variable (p:Pane N) (v:Guard p e)
lemma twist_lagWW (s:Cover)(x:Site N):
 twist (fineryS s N) (WW (x+wrap N s))=WW x:=by
 rw [←mills_lag];exact twist_WW _ false _ x

include h v
lemma sprit_lag (s: Cover)(i:Axis)(y:Site N):
    sprit f g i y (profile (finery s p)) =
     twist (fineryS s N) (sprit f g i (y+wrap N s) (profile p)):=by
  unfold sprit
  rw [show y=(y+wrap N s)+-wrap N s from by abel]
  -- y RHS doubled?
  rw [voyage_map (twist (fineryS s N))
       (v:=fun z x=>firstmate f g z x (profile p))]
  · simp
  intro z x
  obtain ⟨z₁,z₂⟩:=h.parade s p v
  simp only [firstmate,wings,z₁,z₂]
  rw [map_mul,←wind_𝒪]
  have t(w:Site N):twist (fineryS s N) (WW w)= WW (w+-wrap N s):=by
    simpa using twist_lagWW s (w+-wrap N s)
  rw [t,t,add_right_comm x]


lemma bond_lag (s:Cover)(u:Side)(i:Axis)(y:Site N):
  bond f g u i y (profile (finery s p)) =
  twist (fineryS s N) (bond f g u i (y+wrap N s) (profile p)):=by
  unfold bond purl; rw [map_sum]
  refine sum_congr rfl fun x _=>?_
  dsimp only
  rw [sprit_lag h p v,add_right_comm y (wrap N s),add_sub_right_comm (y+wrap N x)]

omit h v in lemma blockStar (u:Side)(x:Site N): IsSelfAdjoint (block u x):=by
 rw [block,isSelfAdjoint_iff,star_sum]
 exact sum_congr rfl fun z _=>(WW_p _).isSelfAdjoint



omit h v in
lemma clear_WW (b:Bool)(x:Site N):
    windX b (WW x)= WW x := by
  cases b
  · rfl
  ext i j
  change star (WW x i j)= _
  have z := WWi x 1 i j
  rw [mul_one] at z
  simp [z,Matrix.one_apply,apply_ite star]

omit h v in
lemma clear_block (b:Bool)(u:Side)(x:Site N): windX b (block u x)=block u x:=by
  simp only [block,win_sum,clear_WW]
omit h v in
lemma tickPin(N):IsStarProjection (tickA N):=by rw [touchP];exact cutM_idp _

lemma lucid (u:Side)(x:Site N):
    star (bust f u x (profile p))=bust f u x (profile p):=by
  simp only [bust,𝒜,sub_mul,Matrix.trace_sub,star_sub,
    ←star_trace_mul (h.pure p v),←star_trace_mul (tickPin N), (blockStar u x).star_eq]

omit h v in
lemma wind_trace {I:Type*}[DecidableEq I][Fintype I](b:Bool)(A:Op I):
    Matrix.trace (windX b A)= if b then star (Matrix.trace A) else Matrix.trace A:=by
  cases b
  · rfl
  change (∑ i,star (A i i))=star (∑ i,A i i)
  exact (star_sum ..).symm


/-- Pseudoscalar BEFORE truncation with both possible charges (full Signed law). -/
theorem signboard (u:Side)(x:Site N)(d:Shape)(b:Bool)(U: UNI SpinIdx)(j:JetS d.s b (detX d.s) U):
    bust f u x (profile (stir (xtra b) d p))=
       let α:=bust f u (finale d x) (profile p)
       if detX d.s then -α else α:=by
  let C:=prepU d U (xtra b) N
  let Φ:=sings b C
  have add(A B): Φ A - Φ B=Φ (A-B):=by unfold Φ; rw [singT,singT,singT,win_l,map_sub]
  have mul(A B): Φ A * Φ B=Φ (A*B):=by unfold Φ; rw [singT,singT,singT,win_m,map_mul]
  let S:=f (profile (stir (xtra b) d p))
  let W:=block u x
  have q:Φ (block u (finale d x))= W:=by unfold Φ; rw [singT,clear_block];exact twist_block d b U u x
  have s₁:Φ (f (profile p))=swapX (detX d.s) S:=(h.step d b U j p v).1
  have s₂:Φ (tickA N)=swapX (detX d.s) (tickA N):=by
    rw [touchP]; exact tickR d _ U j N
  let V :=yoke f u (finale d x) (profile p)
  have tr: Matrix.trace (Φ V)=Matrix.trace V:=by
    have t:star (Matrix.trace V)=Matrix.trace V:=lucid h p v u (finale d x)
    unfold Φ
    simp only [singT,twistTr,wind_trace,t,ite_self]


  change Matrix.trace ((S-tickA N)*W)= if detX d.s then -Matrix.trace V else Matrix.trace V
  rw [←tr]
  unfold V yoke
  rw [←mul,←add,q,s₁,s₂]
  split
  · rename_i t
    simp only [swapX,t,if_true]
    rw [← Matrix.trace_neg, ← neg_mul]
    rw [show -(1-S-(1-tickA N))= S-tickA N from by abel] 
  rename_i t; simp [swapX,t]

/-- Matrix law for O; no equality asserted on J except translations. -/
theorem swan (u:Side)(x:Site N)(d:Shape)(U: UNI SpinIdx)(j:JetS d.s false (detX d.s) U):
    oriole f g u x (profile (stir inert d p)) =
      let W:=oriole f g u (finale d x) (profile p)
      twist (prepU d U inert N) (if detX d.s then star W else W):=by
  obtain ⟨l,s⟩:=h.step d false U j p v
  unfold Cour.yank Thera.jazz at s
  unfold swapX at l
  let P:=prepU d U inert N
  let W:=block u (finale d x)
  let S:=f (profile p)
  let T:=g (profile p)
  let σ:=profile (stir inert d p)
  change twist P S=(if detX d.s then 1-f σ else f σ) at l
  change g σ=(if detX d.s then -star (twist P T) else twist P T) at s


  have q:twist P W=block u x:= twist_block d false U u x
  change 𝒪 (f σ) (g σ) (block u x) = twist P (if detX d.s then star (𝒪 S T W) else 𝒪 S T W)
  rw [←q,s]
  by_cases w:detX d.s=true
  · rw [if_pos w] at l
    have hw : star W=W:= (blockStar ..).star_eq
    rw [if_pos w, if_pos w, ← turn_𝒪 (S:=S) (h.pure p v) T W, hw,←wind_𝒪,
        map_neg,map_sub,map_one,map_star,l,sub_sub_cancel]
  rw [if_neg w] at l
  rw [if_neg w,if_neg w,←wind_𝒪,l]

