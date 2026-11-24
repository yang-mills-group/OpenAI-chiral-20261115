import YM.SU5.Selected.Cor.Rubric
import YM.SU5.Selected.Cor.Fashion
set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 450000
set_option maxRecDepth 3000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Pannier.Chancel.Lantern
open Function Filter NormedSpace Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory ProbabilityTheory Peaks Drapes Rush Tulip Dial Pastry
open Buffered Branch Tenant Skye RG
open Crest.Airy
open Reed (Fine)
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] opCStarAlgebra
namespace Bulb
namespace Mezz
open Stencil
section wedgeC
variable {κ T:Type}[Fintype κ][LinearOrder κ][Fintype T][DecidableEq T]
local notation "L"=> (Finset.univ:Finset T).toList
attribute [local instance] opCStarAlgebra
-- homogeneous counting identities. rotation from double θ linear with (-phase). determinant slice by identifying coeff via Vandermonde.
variable (b:Bool)(A B: UNI κ)(X Z: WRect κ T)
noncomputable def plumeM (A B:UNI κ): FC κ→ₐ[ℂ] FC κ where
  toFun x:= theta A (theta B x)
  map_zero':= by rw [theta_zero,theta_zero]
  map_one':= by rw [theta_one,theta_one]
  map_mul' x y:= by rw [theta_mul,theta_mul]
  map_add' x y:= by rw [theta_add,theta_add]
  commutes' c:= by rw [Algebra.algebraMap_eq_smul_one,theta_smul,theta_smul,theta_one,theta_one,star_star]
lemma plume_letter (x:Ket κ): plumeM A B (creed b x)= -creed b (acts (A*B).val x):= by
 cases b; · change theta A (theta B (create x))=-create _; rw [theta_upV,theta_smul,theta_downV]; simp [smul_smul]
 change theta A (theta B (Fock.remove x))= -Fock.remove _; rw [theta_downV,theta_smul,theta_upV]; simp [smul_smul]
lemma plume_tape (V:WRect κ T)(t:ℂ)(h:(A*B).val* X=t • V) : plumeM A B (tape b X)= (-tone b t)^ (Fintype.card T) • tape b V:=by
 have hf(i:T): plumeM A B (creed b (col X i))=(-tone b t) • (creed b (col V i)):=by rw [plume_letter, ←line_a, h,col_scale,tax_r,neg_smul]
 let v:T→FC κ:= creed b ∘ col X; let z:= creed b ∘ col V; unfold tape party; change plumeM A B (foil v (L))= _ • foil z (L); rw [show (plumeM A B) (foil v _) = foil ((-tone b t) • z) (L) from ?_, foil_scale];
 · simp
 unfold foil; rw [map_list_prod,List.map_map]; exact congrArg List.prod (congrArg (fun f:T→FC κ=> (L).map f) (funext hf))
lemma tape_cov (g:UNI κ): twist (quantU g) (tape b X)= tape b (g.val*X):=by
 have hv(j:T): twist (quantU g) (creed b (col X j))=creed b (col (g.val*X) j):=by rw [line_a]; cases b; exact twist_create ..; exact twist_remove ..
 unfold tape party foil; rw [map_list_prod,List.map_map]; exact congrArg List.prod (congrArg (fun f:T→FC κ=> (L).map f) (funext hv))
private theorem canonP: ∃ u:pulseNode→ℂ,∀ i≤(120:ℕ),∑ k,u k*(pval k:ℂ)^i= if i=1 then 1 else 0:= by
 let f(i:pulseNode):ℂ:= if i.val=1 then 1 else 0; let Y:= Matrix.vandermonde (fun i:pulseNode=> (pval i:ℂ)); have hY: Y.det≠0:= Matrix.det_vandermonde_ne_zero_iff.mpr ((Complex.ofReal_injective).comp (fun i j p=> Fin.ext (Nat.cast_injective (R:=ℝ) ((div_left_inj' (by norm_num : (121:ℝ)≠0)).1 p))))
 obtain ⟨x,h⟩:= (show Surjective (fun w=>Matrix.vecMul w Y) from Matrix.vecMul_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).2 (IsUnit.mk0 _ hY))) f; exact ⟨x,fun i u=>congrFun h (⟨i,by omega⟩:pulseNode)⟩
noncomputable def lyric := canonP.choose
noncomputable def rune (t:pulseNode)(X Z: WRect κ T):= (pval t:ℂ) • X+Z
variable (p:Fintype.card T=10)
include p
lemma loreP : countOne X Z b= ∑ i, lyric i • tape b (rune i X Z):=by
 let x:T→FC κ:= creed b ∘ col X; let z:T→FC κ := creed b ∘ col Z; let F:= range 11
 have e(i:pulseNode): tape b (rune i X Z)= ∑ k∈ F,(pval i:ℂ)^k • rake x z (L) k:=by
    unfold tape party; unfold F; rw [show 11=(L).length+1 from (by rw [rung_len p]),←polish]; congr 1; ext1 j; rw [rune,col_add,col_scale,creed_a,tax_r,tone_real]; rfl
 simp_rw [e,smul_sum,smul_smul]; rw [sum_comm,sum_eq_single 1];
 · unfold lyric; rw [←Finset.sum_smul,show ∑ k,_= _ from canonP.choose_spec 1 (by decide)]; simp; rfl
 · intro i u v; unfold lyric; rw [←Finset.sum_smul, canonP.choose_spec i ?_, if_neg v, zero_smul] -- name lyric unfold
   have hp:= mem_range.mp u; omega
 simp [F]
omit p
end wedgeC
open Stencil (pace pval pulseNode heatize)
open Caste
set_option synthInstance.maxSize 24000
attribute [local instance] opCStarAlgebra
variable {N:Side} {T:Type}[Fintype T][DecidableEq T]
local notation "N'"=> More N
variable (A:Mezz)(P:Society T)(b:Bool)(i:A.Lot)(X Z:Coast→ Wq A.marks)(C:ℝ) (V:Pane N)
local notation "Ω" V:max b:max=> A.pole (N:=N) P i b V X Z C
local notation "S"=> park N (A.yard i.1 b)
local notation "Λ"=> tape
noncomputable def spanOne : FC (Single N):= countOne ((Ω true b) V) ((Ω false b) V) b
noncomputable def matinee : Buffered.Mark N:= fun x=> A.spanOne P b i X Z C x.1
local notation "K"=> A.spanOne (N:=N) P b i X Z C
local notation "ρ"=> A.matinee (N:=N) P b i X Z C
lemma trueMark : (ρ)=toMark (K):=rfl
variable {M:Tulip.Male}{ε:ℝ}{w:ℕ}(c:A.Caste (N:=N) M C ε w X Z)
include c
omit c in
private abbrev weft (d:pulseNode): Pane N→ WRect (Single N) P.Club:= (pval d:ℂ) • (Ω true b)+(Ω false b)
private lemma wefts (d:pulseNode): Coil A P b i (weft (N:=N) A P b i X Z C d):= ((A.windings P b i X Z C c true).scale _).adds (A.windings P b i X Z C c false) -- include c in weft bug
omit c in
lemma meadow_y : (ρ)= ∑ t:pulseNode, lyric t • (fun x:Fields N=> tape b (rune t ((Ω true b) x.1) ((Ω false b) x.1))) := by funext x; change spanOne _ _ b _ _ _ _ _=_; simp_rw [Finset.sum_apply]; exact loreP b _ _ P.club_card
lemma marquee_one : AtSupport false (S) (ρ):= by
 rw [A.meadow_y]
 generalize h: (Finset.univ:Finset pulseNode)=T₁
 clear h; induction T₁ using Finset.induction_on with
 | empty=> rw [sum_empty]; exact AtSupport.zeroM
 | insert d T h H=> rw [sum_insert h]; exact ((wefts A P b i X Z C c d).serves.smulM _).addM H
lemma matinee_c : Continuous (ρ):=by
 rw [A.meadow_y]; generalize h: (Finset.univ:Finset pulseNode)=T₁; clear h; induction T₁ using Finset.induction_on with
 | empty=> rw [sum_empty]; exact continuous_const
 | insert d T h H=> rw [sum_insert h]; exact ( ((tape_c b).comp ((wefts A P b i X Z C c d).cont.comp continuous_fst)).const_smul (lyric d)).add H
lemma matinee_1 (r q:Fields N)(t:r.1=q.1) : (ρ r)=(ρ q):=congrArg (K) t -- defeq
lemma span_cov (g: Seat N→ SU.E) : K (Lattice.gauge g V)= twist (quantU (tradew N g)) (K V):=by
 unfold spanOne; simp_rw [loreP b _ _ P.club_card,map_sum,twist_scalar]; apply sum_congr rfl; intro j _; apply congrArg (fun f:FC (Single N)=> lyric j • f); let A':= P.arm (g ((wrap N') (A.grape i.1 b))); rw [tape_cov];
 let f:= Ω true b; let v:= Ω false b; let Q:= Lattice.gauge g V; let Y:= rune j (f Q) (v Q); change tape b Y = _; rw [show (tradew N g).val*rune j (f V) (v V)=Y*A'.val from ?_, wave_det, P.arm_d, map_one, one_smul]
 unfold Y rune; rw [Matrix.mul_add,Matrix.mul_smul,Matrix.add_mul,Matrix.smul_mul,←polo A P i b true X Z C c g V, ←polo A P i b false X Z C c g V] -- check signature order and let
lemma matinee_g : Buffered.covariant (ρ):=fun g x=> span_cov A P b i X Z C x.1 c g
lemma span_roll : plumeM (carR 0 0 N) (carR 1 0 N) (K (swoop V))= -(K V):= by
 unfold spanOne; simp_rw [loreP b _ _ P.club_card,map_sum,map_smul]; rw [←sum_neg_distrib]; apply sum_congr rfl; intro j hj; rw [plume_tape b _ _ _ _ Complex.I ?_,P.club_card, show (-tone b Complex.I)^(10:ℕ)=(-1:ℂ) from ?_,neg_one_smul,smul_neg]
 · have he(u:ℂ)(h:u^ (2:ℕ)=-1): u^ (10:ℕ)=-1:=by rw [show (10:ℕ)=2*5 from rfl,pow_mul,h]; norm_num
   refine he _ ?_; cases b
   · change (-Complex.I)^(2:ℕ)=-1; rw [neg_sq,Complex.I_sq]
   change (-star Complex.I)^(2:ℕ)=-1; simp [Complex.I_sq]

 rw [←Ro]; unfold rune; rw [Matrix.mul_add,Matrix.mul_smul,pole_roll A P i b true X Z C c,pole_roll A P i b false X Z C c,smul_add,smul_comm]; -- M roll definitional
lemma matinee_R : reflMark 0 0 (reflMark 1 0 (ρ))=-(ρ):=funext fun x=> span_roll A P b i X Z C x.1 c
end Mezz
end Bulb
end YM.CF.Pannier.Chancel.Lantern
open YM.CF.Pannier.Chancel.Lantern.Bulb.Mezz
#print axioms matinee_g
#print axioms marquee_one
#print axioms matinee_R
