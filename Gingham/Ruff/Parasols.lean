import Gingham.Ruff.Coronet
import YM.Next.RANK.Ray
import YM.Planned.ATOM_REGULAR_ESTIMATE.Pin
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 4000
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Gingham.Ruff
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset RG Cube
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Classical
open Skye Scree
local notation "γ"=>SU.group
open Jet Rill Sour Lat Tulip
variable {N:Side}


open Peaks
def clockPin := Classical.choice (Next.Rank.Spindle.charts SU.group)

/-- Physical base certificates independent of tags. -/


structure Pinwax (p:BudgetPoint)(x: Seat N)(q:ℕ)(U:Pane N) where
  color: Seat N→SU.E
  grip(i: Edge (Seat N)): separation x i.1≤ q →
    SU.group.chord (gauge color U i)≤ 4*(p.threshold*(1+(separation x i.1:ℝ)))

variable {x:Seat N}{p:BudgetPoint}{U: Pane N}

lemma pinwaxes (q:ℕ)(j: 2*(q+1)< (More N).val)
   (h:pingS p.threshold (Lattice.halo (q+1) {x}) U):
   Nonempty (Pinwax p x q U):=by
   obtain ⟨c,z⟩:= Planned.AtomRegular.Foliage.Cube.anchored x (ping_le h)
      p.threshold_pos.le le_rfl j
   exact ⟨c,z⟩

def liltCost (p:BudgetPoint)(ρ:ℝ)(m:ℕ):ℝ:=
  p.threshold * (8*(1+(m:ℝ)))/ρ


variable {q:ℕ}{ρ:ℝ}

structure Parasols(p:BudgetPoint)(ρ:ℝ)(q:ℕ):Prop where
  shade: 4*(p.threshold*(1+(q:ℝ))) ≤ clockPin.c
  fine: liltCost p ρ q < 1
  pos: 0<ρ

variable (P:Parasols p ρ q)

include P
lemma small_lilt(m:ℕ)(j:m≤q): liltCost p ρ m < 1:=
  (show liltCost p ρ m ≤ liltCost p ρ q from div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by gcongr) p.threshold_pos.le)
    P.pos.le).trans_lt P.fine
lemma rich_lilt(m:ℕ): 0<p.threshold/ρ ∧ p.threshold/ρ ≤ liltCost p ρ m:=
  ⟨div_pos p.threshold_pos P.pos, div_le_div_of_nonneg_right 
      (le_mul_of_one_le_right p.threshold_pos.le (by linarith only [(Nat.cast_nonneg (α:=ℝ) m)])) P.pos.le⟩

omit P

def baseL (ρ:ℝ)(m:ℕ)(g:Pinwax p x q U): Doub N:=
 (0,fun i=>if separation x i.1 ≤ m then
  ρ⁻¹ • SU.group.plog (SU.group.mat (Lattice.gauge g.color U i)) else 0)

private lemma eachShade (g:Pinwax p x q U) (m:ℕ)
   (i:Edge (Seat N))(t:separation x i.1 ≤ m)(w:m≤q):
   SU.group.chord (gauge g.color U i) ≤ 4*(p.threshold*(1+(m:ℝ))):=by
 have a:=p.threshold_pos
 refine (g.grip _ (t.trans w)).trans ?_
 gcongr


include P
lemma base_length (m:ℕ)(g:Pinwax p x q U)(j:m≤q):
 ‖baseL ρ m g‖≤ liltCost p ρ m:=by
 have ht:=P.pos
 have a:0≤ liltCost p ρ m :=(rich_lilt P m).1.le.trans (rich_lilt P m).2
 rw [Prod.norm_def]
 refine max_le (by rw [show (baseL ρ m g).1=0 from rfl,norm_zero];exact a) ((pi_norm_le_iff_of_nonneg a).mpr (fun i=>?_))
 unfold baseL; dsimp only
 split
 · next t=>
   rw [norm_smul,norm_inv,Real.norm_of_nonneg ht.le]
   have hv:=clockPin.sleeve _ ((eachShade g q i (t.trans j) le_rfl).trans P.shade)
   refine (mul_le_mul_of_nonneg_left (hv.trans (mul_le_mul_of_nonneg_left 
      (eachShade g m i t j) (by positivity))) (inv_nonneg.mpr ht.le)).trans ?_
   unfold liltCost
   exact le_of_eq (by ring)
 rw [norm_zero];exact a

lemma lilt_record (g:Pinwax p x q U)(m:ℕ)(i:Edge (Seat N))
    (t:separation x i.1 ≤ m)(w:m≤q):
 SU.group.lieExp (ρ • (baseL ρ m g).2 i)=(gauge g.color U) i:=by
 simp only [baseL,t,if_true,smul_smul,mul_inv_cancel₀ P.pos.ne',one_smul]
 exact clockPin.records _ ((eachShade g q i (t.trans w) le_rfl).trans P.shade)



omit P
variable {Y:Type}[NormedAddCommGroup Y][NormedSpace ℝ Y]
def spinweed (g:Pinwax p x q U): tangD N→L[ℝ]tangD N:=
 LinearMap.toContinuousLinearMap
    {toFun:=fun t i=>SU.group.adjoint (g.color i.1) (t i)
     map_add':=fun a b=>by ext; simp
     map_smul':=fun c a=>by ext; simp}

lemma spinweed_eq (g:Pinwax p x q U)(y:tangD N)(i:Edge (Seat N)):
 spinweed g y i=SU.group.adjoint (g.color i.1) (y i):=rfl

def zydeco(ρ:ℝ)(g:Pinwax p x q U)(T:Y→L[ℝ]tangD N): Y→L[ℝ] Doub N:=
 ((p.threshold/ρ) • ((spinweed g).comp T)).prod 0

include P
lemma zydeco_bill(g:Pinwax p x q U)(T:Y→L[ℝ]tangD N)(h:‖T‖≤1):
 ‖zydeco ρ g T‖ ≤ p.threshold/ρ:=by
 have k:0≤p.threshold/ρ:=(rich_lilt P 0).1.le
 apply ContinuousLinearMap.opNorm_le_bound _ k
 intro v
 rw [Prod.norm_def]
 refine max_le ?_ ?_
 · change ‖(p.threshold/ρ) • spinweed g (T v)‖≤_
   rw [norm_smul,Real.norm_of_nonneg k]
   refine mul_le_mul_of_nonneg_left ((pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr (fun i=>?_)) k
   simpa [spinweed_eq] using show ‖(T v) i‖ ≤ ‖v‖ from 
    (norm_le_pi_norm _ _).trans ((T.le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg v) h))

 change ‖(0:tangD N)‖≤_
 rw [norm_zero]
 exact mul_nonneg k (norm_nonneg _)

/-- Does not require that the incremented first Pane pass the Guard test. -/
lemma tune_up(g:Pinwax p x q U)(T:Y→L[ℝ]tangD N)(m:ℕ)(j:m≤q)
    (v:Y)(i:Edge (Seat N))(u:separation x i.1≤ m):
 (pencil ρ (baseL ρ m g + zydeco ρ g T v)) i =
 gauge g.color (increment U (p.threshold • T v)) i:=by
 have z : (baseL ρ m g).1=0:=rfl
 have a:(zydeco ρ g T v).1 i=(p.threshold/ρ) • SU.group.adjoint (g.color i.1) (T v i):=rfl
 have b:(zydeco ρ g T v).2=0:=rfl
 simp only [pencil,Prod.fst_add,Prod.snd_add,b,add_zero,
   lilt_record P g m i u j,z,zero_add,a,smul_smul,
   mul_div_cancel₀ p.threshold P.pos.ne'] -- last?
 rw [←map_smul, Next.SectorChange.exp_adjoint]
 unfold Lattice.gauge increment; rw [Pi.smul_apply]
 group

