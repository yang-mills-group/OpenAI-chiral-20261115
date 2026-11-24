import YM.SU5.May.FloePrice
import YM.SU5.May.TorqueCap
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option synthInstance.maxSize 30000
set_option maxRecDepth 3000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.May.TorqueBeam
open Function Filter Finset Fir Lattice Laurent Next.Free Bloch Lat Ember Jill Rush
open scoped Topology BigOperators ContDiff InnerProductSpace Matrix MatrixOrder Kronecker Matrix.Norms.L2Operator Classical
attribute [local instance] opCStarAlgebra
open Onyx Fock SU Flare Kea Sods Emu Dial Cube Tulip Spire Scroll Thera
open Fock Reflect
open Lamour (lakeP lakeK)
open Hygrometry Personality PriceCliff
open RG Wilson Phase Mir Vale Vale.Grace Peaks Paige Vault
open Stationary (Gaia)
open Buffered.Lifted Buffered.Afterglow.Tower.Tilted
open scoped ComplexOrder
local notation "Ω" => Complex.I
open May.Floe
open Buffered Buffered.Advance Buffered.Advance.Whorl May.Arctic
variable {I:Type*}[LinearOrder I] [Fintype I] (U:UNI I)(L:Op I)(b:Bool)(δ:ℝ)
noncomputable def send (x:Reader0 I): Reader0 I:= (!x.1,-acts U.val x.2)
noncomputable abbrev costal (x:Reader0 I):ℂ:= ActMark.applause x.1
private lemma keyShift {x:Reader0 I} {T:Finset I}(p:twist U (cutM Tᶜ)=cutM T)(h: withinM (if x.1 then Tᶜ else T) x.2): withinM (if (send U x).1 then Tᶜ else T) (send U x).2 :=by
 have he {A B:Finset I}(q:twist U (cutM A)=cutM B){v:Ket I}(p:withinM A v): withinM B (-acts U.val v):=by
    unfold withinM; rw [map_neg,←act_mul,←q,twist_product,act_mul,p]
 rcases x with ⟨⟨⟩,v⟩; exact he (Reed.Fine.altitude p) h; exact he p h
lemma markSend {N:Side} (P:Ramp) {x:Reader0 (Single N)}(h:KeyT x (tickA N)) : KeyT (send (P.vehicle N) x) (tickA N):=by
 have he(x:Reader0 (Single N)): KeyT x (tickA N) ↔ withinM (if x.1 then (Tset N)ᶜ else Tset N) x.2:= by rw [KeyT,touchP]; cases x.1 <;> simp only [Bool.false_eq_true,ite_false,ite_true,within_compl,withinM]
 exact (he _).mpr (keyShift (P.vehicle N) (P.exchanges N) ((he _).1 h))
lemma mark_send (x:Reader0 I): theta U (ton x)= costal x • ton (send U x):=by
 rcases x with ⟨⟨⟩,u⟩
 · change theta U (create u)=Complex.I • remove (- acts U.val u); rw [theta_upV]; simp [Fock.remove]
 change theta U (remove u)= (-Complex.I) • create (- acts U.val u); rw [theta_downV]; simp
lemma costal_f {x:Reader0 I}: ‖costal x‖=1:=by cases q:x.1<;> simp_all [costal, ActMark.applause] -- simp needs he
-- complex (including reality) obstruction. sharp tester.
noncomputable def wickRay (u v:Ket I):ℂ:=if b then -(inner ℂ v (acts L (acts U.val u)))+(δ:ℂ)*inner ℂ v u else -(inner ℂ (acts U.val u) (acts L v))+(δ:ℂ)*inner ℂ u v
-- define charge ANY planned.Grants no unnamed rank assumption
noncomputable def WickPlate (A S: Finset I):Prop:=∀ (b:Bool)(x:Ket I), withinM (if b then Aᶜ else A) x → withinM S x →0 ≤ wickRay U L b δ x x
noncomputable def promoted (x y:Reader0 I):ℂ:= if x.1=y.1 then wickRay U L x.1 δ x.2 y.2 else 0
lemma fromRank (x y:Reader0 I): promoted U L 0 x y=Complex.I*costal x*rankG L (send U x) y:=by
 rcases x with ⟨⟨⟩,x⟩ <;> rcases y with ⟨⟨⟩,y⟩<;> simp [promoted,wickRay,rankG,send,costal,ActMark.applause]
lemma normRise (h:0≤δ)(x y: Reader0 I): ‖promoted U L δ x y-promoted U L 0 x y‖ ≤ δ*(‖x.2‖*‖y.2‖):=by
 unfold promoted; split_ifs with p; swap; · simp; positivity -- tune
 unfold wickRay; split <;> simp only [Complex.ofReal_zero,zero_mul,add_zero,add_sub_cancel_left,norm_mul,Complex.norm_real, Real.norm_of_nonneg h] <;> (refine mul_le_mul_of_nonneg_left ?_ h; (first| exact norm_inner_le_norm ..| exact (norm_inner_le_norm ..).trans_eq (mul_comm ..)))
variable {α:Type*}
private lemma twoPly (F:Finset α)(X:α→Ket I)(w:α→ℂ): wickRay U L b δ (∑ i∈F,(if b then star (w i) else w i) • X i) (∑ i∈F,(if b then star (w i) else w i) • X i)= ∑ i∈ F, ∑ k ∈F, star (w i)*wickRay U L b δ (X i) (X k)*w k:=by
 cases b
 · simp_rw [wickRay, Bool.false_eq_true, if_false, map_sum,map_smul, sum_inner,inner_sum,inner_smul_left,inner_smul_right]; simp_rw [←Finset.sum_neg_distrib,Finset.mul_sum, mul_add,add_mul, Finset.sum_add_distrib]; congr 1 <;> apply sum_congr rfl <;> intro i _ <;> apply sum_congr rfl <;> intro k _ <;> (rw [← Complex.star_def]; ring)
 simp_rw [wickRay, if_true, map_sum,map_smul, sum_inner,inner_sum, inner_smul_left,inner_smul_right,← Finset.sum_neg_distrib, Finset.mul_sum, mul_add, add_mul,Finset.sum_add_distrib,← Complex.star_def,star_star]; congr 1<;> rw [sum_comm] <;> apply sum_congr rfl <;> intro i _ <;> apply sum_congr rfl <;> intro k _ <;> ring
lemma raiseP (X:α→ Reader0 I){ρ:ℝ}{A S:Finset I}(W:∀ i,Worth A S ρ (X i))(h: WickPlate U L δ A S) [LinearOrder α][Fintype α]: 0 ≤ (Matrix.of fun i j:α=> promoted U L δ (X i) (X j)):=by
 set T:= Matrix.of (fun i j:α=> promoted U L δ (X i) (X j)); apply sprite_nonneg; intro w; let D(b:Bool):= (Finset.univ:Finset α).filter (fun x=>(X x).1=b)
 let Φ(i j:α):= star (w i)* promoted U L δ (X i) (X j)*w j
 have h0(i j:α)(h:(X i).1≠ (X j).1):Φ i j=0:=by simp [Φ,promoted,h]
 have hs(b):0≤∑ i∈ D b,∑ j∈D b,Φ i j:=by
    let Y:=fun v:α=>(X v).2; let S₀:=∑ i∈D b,(if b then star (w i) else w i) • Y i
    have he(i:α)(p:i∈D b):(X i).1=b:= (mem_filter.mp p).2
    have hf(K: Finset I)(p:∀ i∈D b,withinM K (Y i)): withinM K S₀:=by unfold withinM S₀; rw [map_sum]; exact sum_congr rfl (fun i w => by rw [map_smul,p i w])
    refine (h b S₀ (hf _ fun i Q=>he i Q ▸ (W i).limb) (hf _ fun i _=>(W i).touches)).trans_eq ?_; unfold S₀; rw [twoPly]; apply sum_congr rfl; intro i p; exact sum_congr rfl fun j g=> by simp [Φ,promoted,he i p,he j g,Y]
 have he: Finset.univ=D true∪D false:=by ext x; cases u:(X x).1<;> simp [D,u]
 have hd: Disjoint (D true) (D false):= by apply Finset.disjoint_left.mpr; intro i p k; exact (show true≠false by decide) ((mem_filter.mp p).2.symm.trans ((mem_filter.mp k).2))
 change 0 ≤ ∑ i,∑ j,Φ i j; rw [he, sum_union hd]; try simp_rw [sum_union hd]
 rw [sum_add_distrib,sum_add_distrib]; have ht(b c:Bool)(p:b≠c):∑ i∈ D b,∑ j∈ D c,Φ i j=0:=sum_eq_zero (fun i hs=> sum_eq_zero fun j h'=> h0 i j (by rw [(mem_filter.mp hs).2,(mem_filter.mp h').2]; exact p)); rw [ht true false (by decide), ht false true (by decide),add_zero,zero_add]; exact add_nonneg (hs _) (hs _)
#print axioms raiseP
end YM.CF.May.TorqueBeam
