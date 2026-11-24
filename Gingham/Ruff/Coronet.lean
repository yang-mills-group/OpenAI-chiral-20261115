import YM.CF.Sour.Fro
import YM.CF.Skye.Man
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


abbrev Doub(N:Side):=tangD N × tangD N

/-- X=(new directions, base log), scaled both in sup norm. -/
def pencil (ρ:ℝ)(x:Doub N): Pane N:= fun i=>
 SU.group.lieExp (ρ • x.1 i) * SU.group.lieExp (ρ • x.2 i)
def dabble (ρ:ℝ)(x:Doub N):Pane N:= if ‖x‖<1 then pencil ρ x else 1
lemma pencil_flat (ρ:ℝ): pencil (N:=N) ρ 0=1:=funext fun i=>by simp [pencil]

lemma flag_gentle {n:Side}(U:Pane n){t:ℝ}
   (h:∀i,SU.group.chord (U i)≤t/4): flags (G:=γ) t U=∅:=by
  apply Skye.broad
  intro i
  unfold faceValue square
  simp only [travel,Step.pos_read, Step.neg_read,Step.vec_neg,Step.vec_pos,mul_one]
  apply le_trans (SU.group.chord_triangle ..)
  refine le_trans (add_le_add (h _) ?_) (show t/4+(t/4+(t/4+t/4))≤t from by linarith)
  apply le_trans (SU.group.chord_triangle ..)
  apply add_le_add (h _)
  apply le_trans (SU.group.chord_triangle ..)
  rw [Gauge.chord_inv,Gauge.chord_inv]
  exact add_le_add (h _) (h _)


lemma lets_pencil {e:ℝ}(h:0<e):∃ d:ℝ,0<d∧
    ∀ (ρ:ℝ),0≤ρ→ρ≤d→∀ (N:Side)(x:Doub N),Guard (dabble ρ x) e:=by
  obtain ⟨t,ht,H⟩:=taxon h
  have key: ∀ᶠ u:SU.group.Color in 𝓝 0,SU.group.chord (SU.group.lieExp u)<t/8:=
    ((SU.group.continuous_chord.comp SU.group.lieExp_cont).tendsto 0).eventually
      (gt_mem_nhds (by simp; positivity))
  obtain ⟨d,l,v⟩:= nhds_basis_closedBall.eventually_iff.mp key
  refine ⟨d,l,fun ρ y z N x=>H N _ (flag_gentle _ (fun i=>?_))⟩
  unfold dabble
  split
  · next hx=>
    have f(r:tangD N)(w:‖r‖≤1):SU.group.chord (SU.group.lieExp (ρ • r i))≤t/8:=by
      apply le_of_lt (v _); exact mem_closedBall_zero_iff.mpr (by
        rw [norm_smul, Real.norm_of_nonneg y]; exact
          (mul_le_of_le_one_right y ((norm_le_pi_norm ..).trans w)).trans z)
    rw [Prod.norm_def,max_lt_iff] at hx
    exact (SU.group.chord_triangle ..).trans ((add_le_add (f x.1 hx.1.le)
        (f x.2 hx.2.le)).trans (by linarith))
  change SU.group.chord 1≤t/4; rw [Gauge.chord_one];positivity


def Lukewarm (t:ℕ)(ρ b:ℝ):Prop:=∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]
   (V W:E→L[ℝ]SU.group.Color)(u:E), ‖V‖≤1→‖W‖≤1→ ‖u‖≤1→ 
 Tender (fun v=>SU.group.lieExp (ρ • V v)* SU.group.lieExp (ρ • W v)) u b t

open scoped Matrix.Norms.Frobenius in
lemma salve (t:ℕ)(b d:ℝ)(h:0<b)(h0:0<d):∃ ρ:ℝ,0<ρ∧ρ≤d∧ Lukewarm t ρ b:=by
 obtain ⟨C,k,H⟩:=funding t
 obtain ⟨a,l,D,j,J⟩:=Rill.buy _ t (duoK t (·*·) (by
   intro x y f g;unfold Err.Scope; simp_rw [Function.comp_def,Gauge.mat_mul];exact f.mul g))
 have hC:=zero_lt_one.trans_le k
 have hD:=zero_lt_one.trans_le j
 let ρ:=min d (min 1 (min (a/C) (b/D/C)))
 have hx:0<ρ:=lt_min h0 (lt_min zero_lt_one (lt_min (by positivity) (by positivity)))
 have ht:ρ≤d∧ρ≤1∧(ρ≤a/C∧ρ≤b/D/C):=by
   simp [ρ]
 refine ⟨ρ,hx,ht.1,?_⟩


 intro E g p V W u v w r
 have one(X:E→L[ℝ]SU.group.Color)(e:‖X‖≤1):Tender
      (fun i:E=>SU.group.lieExp (ρ • X i)) u (C*ρ) t:=
   H _ (F:=fun i:E=>ρ • X i) _
       ((Allows.smul (allows_linear e ((X.le_opNorm u).trans (mul_le_one₀ e (norm_nonneg _) r))) ρ).mono
         (by rw [abs_of_pos hx,mul_one]))
       ht.2.1
 have ac:C*ρ≤a:=(mul_comm C ρ).le.trans ((le_div_iff₀ hC).mp ht.2.2.1)
 exact (J.duty ac (one V v) (one W w)).bag
   (show D*(C*ρ)≤ b by
     rw [mul_comm D,mul_comm C]
     exact (le_div_iff₀ hD).mp ((le_div_iff₀ hC).mp ht.2.2.2))


structure Rialto (n:ℕ)(e ρ b:ℝ):Prop where
  strict:0<e
  good(N:Side)(x:Doub N): Guard (dabble ρ x) e
  action : actB e n b
  warm:Lukewarm n ρ b

lemma libretto(n:ℕ)(e:ℝ)(h:0<e):∃ ρ b,0<ρ ∧ Rialto n e ρ b:=by
 obtain ⟨d,v,Q⟩:= lets_pencil h
 obtain ⟨b,p,w⟩:= opus_b n h
 obtain ⟨ρ,a,z,t⟩:=salve n b d p v
 exact ⟨ρ,b,a,h,Q _ a.le z,w,t⟩

open scoped Matrix.Norms.L2Operator
open Peaks

variable {e ρ b:ℝ}{n:ℕ}
def pate (h:Rialto n e ρ b)(x:Doub N): ↥(Openc (More N) e):=
 ⟨Tulip.profile (dabble ρ x),dabble ρ x,h.good N x,by simpa using h.strict⟩

abbrev picks (k:Edge (Seat N)) : tangD N →L[ℝ] SU.group.Color:=
  ContinuousLinearMap.proj k


open scoped Matrix.Norms.Frobenius in
lemma dabble_paid (h:Rialto n e ρ b)(x:Doub N)(v:‖x‖<1)(i:Edge (Seat N)):
 Tender (fun y=> dabble ρ y i) x b n:=by
 let f:= ContinuousLinearMap.fst ℝ (tangD N) (tangD N)
 let g:= ContinuousLinearMap.snd ℝ (tangD N) (tangD N)
 let X:= (picks i).comp f
 let Y:= (picks i).comp g
 have z:‖X‖≤1:= X.opNorm_le_bound zero_le_one fun j=>
   ((norm_le_pi_norm (f j) i).trans ((show ‖j.1‖≤ ‖j‖ from by rw [Prod.norm_def];exact le_max_left ..).trans_eq (one_mul _).symm))
 have t:‖Y‖≤1:= Y.opNorm_le_bound zero_le_one fun j=>
   ((norm_le_pi_norm (g j) i).trans ((show ‖j.2‖≤ ‖j‖ from by rw [Prod.norm_def]; exact le_max_right ..).trans_eq (one_mul _).symm))
 exact (h.warm X Y x z t v.le).same
    (((continuous_norm (E:=Doub N)).tendsto x).eventually (gt_mem_nhds v) |>.mono fun u c=>by
       change SU.group.mat ((pencil ρ u) i)=SU.group.mat ((dabble ρ u) i)
       rw [dabble,if_pos (show ‖u‖<1 from c)])

#print axioms libretto

