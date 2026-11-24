import YM.SU5.FiniteGaugeData.Largo.Sonar
import YM.SU5.FiniteGaugeData.Largo.Plume
import YM.CF.Rush.Knoll
set_option linter.unusedSimpArgs false
set_option autoImplicit false
set_option maxHeartbeats 320000
noncomputable section
namespace YM.CF.Window.Largo
open Function Filter Lattice Metric Complex Finset Laurent Next.Free Bloch Fir Lat MeasureTheory Fock Rush
open scoped Topology BigOperators Pointwise ENNReal Matrix Matrix.Norms.L2Operator MatrixOrder InnerProductSpace ComplexOrder Kronecker
attribute [local instance] opCStarAlgebra
-- rents and time projection comm.
variable {N:Side} (M:Tulip.Male)(b:Bool)(A: Op (Mini N))
abbrev ruddy (N:Side): Finset (Mini N):= univ ×ˢ Lat.plusHalf
private lemma airy : cutM (ruddy N)= E₁ (fun _=> Aop) N:=by
 unfold E₁; rw [pilesV]; ext ⟨x,i⟩ ⟨y,j⟩; rw [jump_apply, Adef,← raising]; by_cases h:x=y <;> by_cases p:i=j <;> by_cases t:i∈plusHalf <;> simp_all [ruddy,cutM,Matrix.diagonal_apply,h,t]
abbrev scel (N:Side): Finset (Mini N):=(ruddy N)ᶜ
lemma mark_scel : cutM (scel N)= E₁ (fun _=>1-Aop) N:=by unfold E₁; rw [←pilesM (g:=fun _=>Aop), piles1]; have he: plates N (fun _=>Aop)=cutM (ruddy N):= airy.symm; rw [he,←cutM_read' (ruddy N)]; change _=_ + cutM (scel N)-_; abel
lemma scel_sign (x:Mini N): x∈ scel N ↔ x.2∉Lat.plusHalf:= by simp [scel,ruddy]
abbrev flatH (M:Tulip.Male)(N:Side):= E₁ (bar 4 M.val) N
local notation "ζh"=> flatH M N
local notation "R"=> reedsK M N
lemma flatH_pro : IsStarProjection (flatH M N):=by
 constructor
 · unfold IsIdempotentElem flatH E₁; rw [pilesP]; exact pilesE _ _ fun p u e=> (bar_frames _ _ u e M.property).1
 unfold IsSelfAdjoint flatH E₁; rw [pilesS]; exact pilesE _ _ fun p u e=> (bar_frames _ _ u e M.property).2
private lemma pilesZe : plates N (fun _=> (0:Op SpinIdx))=0:=by rw [← sub_self (plates N (fun _=> (1:Op SpinIdx))),pilesM]; simp
lemma reeds_s : cutM (ruddy N)*reedsK M N = reedsK M N*cutM (scel N) := by
 rw [airy,mark_scel]; unfold E₁ reedsK; rw [pilesP,pilesP]; exact pilesE _ _ fun p u e=>by simp only [mul_neg,neg_mul, zenA]
lemma reeds_shift : cutM (scel N)*R = R* cutM (ruddy N):=by
 rw [airy,mark_scel]; unfold E₁ reedsK; rw [pilesP,pilesP]; exact pilesE _ _ fun p u e=>by simp only [mul_neg,neg_mul, zenAA]
lemma flatH_loan : ζh*(1+R)*cutM (scel N)= 0 := by
 rw [mark_scel]; unfold flatH reedsK E₁; rw [← piles1 (N:=N), pilesA,pilesP, pilesP,←pilesZe]; apply pilesE; intro p u e; let v:=mixL 4 M.val p; rw [(bar_full _ _ u e (graphs_ne (phys_mix _ _ M.property _ u.1))).1]; let C:=zen v; let s:= shell 4 M.val p; change s • ((1-C)*Aop*(1+C)) * (1+-C)*(1-Aop)=0
 rw [Matrix.smul_mul, Matrix.smul_mul,←sub_eq_add_neg, mul_assoc ((1-C)*Aop), show (1+C)*(1-C)=(1+prodM v v) • (1:Op SpinIdx) from ?_, Matrix.mul_smul,mul_one, Matrix.smul_mul, mul_assoc (1-C),mul_sub Aop,mul_one,AOne,sub_self,mul_zero,smul_zero,smul_zero]; rw [add_mul,one_mul,mul_sub,mul_one,show C*C=-(prodM v v) • 1 from zenSq v]; module
-- Time sets. chronology.
def terraceH (N:Side)(h:ℕ) : Finset (Per N) := (Icc (-(h:ℤ)) h).image fun i:ℤ=>(i:Per N)
def clock (J:Finset (Per N)) : Finset (Mini N) := univ.filter fun i:Mini N=> i.1 3∈ J
abbrev Aeons (N:Side)(h:ℕ): Finset (Mini N):= clock (terraceH N h)
lemma Aeons_mem (v: Mini N)(h:ℕ): v∈Aeons N h ↔ ∃ a:ℤ, ((a:Per N)=v.1 3) ∧ -(h:ℤ)≤ a ∧ a≤ h:=by simp [Aeons, clock, terraceH, and_comm]
lemma aeons_mono (v h:ℕ)(p:v≤h): Aeons N v⊆Aeons N h:=by intro i x; obtain ⟨a,b,c,d⟩:= (Aeons_mem ..).mp x; exact (Aeons_mem ..).mpr ⟨a,b,by omega,by omega⟩
def Ballroom (V:Finset (Mini N)): Prop:=∀ i j:Mini N,i.1 3=j.1 3→i.2=j.2→ i∈V→ j∈V
namespace Ballroom
variable {V Q:Finset (Mini N)}
lemma canePos (h:Ballroom V): Commute (cutM V) (Cane N).val:=cutSpan_comm _ _ fun i j p=> by
 obtain ⟨a,b⟩:= not_not.mp (mt (Cane_zero (N:=N) i j) p); exact ⟨h i j a b, h j i a.symm b.symm⟩
lemma caneEq (h:Ballroom V): twist (Cane N) (cutM V)=cutM V:=by rw [twist_formula,← h.canePos.eq,mul_assoc, (show (Cane N).val * star (Cane N).val=1 from (Cane N).property.2),mul_one]
lemma within_compl(h:Ballroom V): Ballroom Vᶜ := by intro i j a b; simp; exact mt (h _ _ a.symm b.symm)
lemma within_inter(h:Ballroom V)(p:Ballroom Q): Ballroom (V∩Q):= fun i j a b runH=> mem_inter.mpr ⟨h i j a b (mem_inter.mp runH).1,p _ _ a b (mem_inter.mp runH).2⟩
lemma timely(A:Finset (Per N)): Ballroom (Largo.clock A):=by intro i j a b; simp [Largo.clock,a]
lemma Ruddy : Ballroom (ruddy N) := by intro i j a b; simp [ruddy,b]
lemma Scer : Ballroom (scel N):= Ruddy.within_compl
lemma Awesome(n:ℕ): Ballroom (Aeons N n) := timely _
end Ballroom
section hprog
variable (r d:ℕ)(V:Momentum→Op SpinIdx){j:Cover}{i k:Mini N}
private lemma bookL (h:j∈Lattice.box d)(x:wagon N (tub V) j k i≠0) (p:i∈ Aeons N r): k∈ Aeons N (r+d):=by
 obtain ⟨J,q⟩:=i; obtain ⟨Z,v⟩:=k; obtain ⟨f,y,b,t⟩:= (Aeons_mem ..).mp p; have he: Z+wrap N j=J:= (by contrapose! x; rw [wagon_app]; exact if_neg x); have hg:= box_test.mp h; have hZ:(Z+wrap N j) 3=f:= by rw [he]; exact y.symm
 apply (Aeons_mem ..).mpr; refine ⟨f-j 3,?_,by specialize hg; have h: j 3 ≤ d:= hg.2 _; omega,by have h:= hg.1 (3:Axis); omega⟩; simp only [Int.cast_sub]; change (f:Per N)- _=Z 3; exact sub_eq_of_eq_add hZ.symm
lemma prolong : cutM (Aeons N (r+d)) * plateH V N d * cutM (Aeons N r)= plateH V N d * cutM (Aeons N r):=by
 ext i j; rw [compass',compass',compass]; split_ifs with h t; rfl; · unfold plateH; rw [Matrix.sum_apply]; refine (sum_eq_zero fun z K=> ?_).symm; exact not_not.mp (fun p=> t (bookL r d V K p h))
 rfl -- tune split.
-- Film Good: projections back ∈ some Tang keys, cardinal. 
variable (p:Finset (Stereo N))
abbrev films (p:Finset (Stereo N)) : Finset (Mini N):= univ.filter fun k=> back k.1∈p
def FrameP (p: Finset (Stereo N)) : Op (Mini N):= twist (Cane N) (cutM (films p))
@[simp] lemma fmem (p:Finset (Stereo N))(i): i∈films p↔ back i.1∈p:= mem_filter.trans (and_iff_right (mem_univ _))
lemma inn : Commute (cutM (films p)) (adagio V N):= cutSpan_comm _ _ fun i j h=>by simp_rw [fmem, (show back i.1=back j.1 from (not_not.mp (mt (adagio_h V i j) h)))]
lemma innE : Commute (FrameP p) (E₁ V N):=by rw [alf]; exact Commute.map (inn V p) (twist ..)
namespace Curtain
variable {e C:ℝ} {Q:Finset (Stereo N)}
def Hired (p:Finset (Stereo N)) : Prop:=∀ i∈p, Slab (badge i)
lemma hired (h:e≥0)(z:C≥0)(runH:∀ v:Stereo N, v∈Q→ Ream (shineF (stairF 4 (badge v) M)) e C) (p:Hired Q) (U V:Finset (Mini N))(q:Ballroom U)(t:Ballroom V)(X:ℝ) (x:0≤X) (v:∀ i:Stereo N,i∈Q→ ‖cutM U* E₁ (shineF (stairF 4 (badge i) M)) N *cutM V‖ ≤ X) : ‖cutM U * reedsK M N * FrameP Q * cutM V‖ ≤ X :=by
 let P:= cutM (films Q); let α(i:Stereo N): Finset (Mini N):= films {i}; let Φ:=fun x=> -zen (mixL 4 M.val x); let A:= cutM U *adagio Φ N*cutM V; have hx: Commute (FrameP Q) (cutM V):= by
    rw [show cutM V = twist (Cane _) (cutM V) from t.caneEq.symm]; exact (cutM_com ..).map _
 rw [mul_assoc (_*_),hx.eq,←mul_assoc]; rw [←t.caneEq,←q.caneEq, reedsK, alf, FrameP,← map_mul,← map_mul,←map_mul,twist_norm]; change ‖A*P‖≤ _
 have hu:Pairwise (Function.onFun Disjoint α):=fun i j t=> disjoint_left.mpr fun k v g=> t (by unfold α at *; simp at g v; rw [←v,←g]); -- types implicit
 have hp:P=∑ i∈ Q, cutM (α i):= by
    ext i j; rw [Matrix.sum_apply]; by_cases h:i=j; swap; · simp [P,cutM,h]
    subst j; simp only [P,cutM,Matrix.diagonal_apply_eq,fmem,α,mem_singleton]; -- target
    rw [Finset.sum_ite_eq]; -- equality tune
 let f(i):= A*cutM (α i); have hg(i:Stereo N): cutM (α i)*cutM (α i)=cutM (α i):=(cutM_idp _).1
 have hz(i:Stereo N): f i = cutM U*adagio Φ N*cutM (α i) *cutM V:=by unfold f A; rw [mul_assoc (_*_) (cutM V), (cutM_com ..).eq,←mul_assoc]
 rw [hp, Matrix.mul_sum]; refine coast_sumPay f α α x Q hu hu ?_ ?_ ?_
 · intro i _; let a:=cutM (α i); let W:=cutM V; let L:=cutM U; have hx: Commute a A:= ((cutM_com ..).mul_right (inn Φ _)).mul_right (cutM_com ..); unfold f; rw [←mul_assoc,hx.eq,mul_assoc,hg]
 · intro i _; unfold f; rw [mul_assoc,hg]
 intro i w; let S:=shineF (stairF 4 (badge i) M); let T:=cutM U*adagio S N*cutM V; have he:adagio Φ N*cutM (α i)=adagio S N * cutM (α i):=by
    ext j k; rw [compass',compass']; split_ifs with g; swap; · rfl
    by_cases h:back j.1=back k.1; swap; · rw [adagio_h Φ j k h, adagio_h S j k h]
    have hm: back k.1=i:=mem_singleton.mp (fmem ..|>.mp g); have hx(p':Mini N)(h: back p'.1=i): ∃ t j,p'=debut i t j:=⟨p'.1 3,p'.2,by unfold debut; rw [← h,full_back]⟩
    obtain ⟨x,w',rfl⟩:= hx j (h.trans hm); obtain ⟨g,u,rfl⟩:=hx k hm; rw [adagio_formula,adagio_formula, if_pos rfl, if_pos rfl]; refine Finset.sum_congr rfl fun k _=>?_ ; unfold Φ S; simp_rw [shineF]; rw [coast_reel (badge i) (p i w) M 4 (base_subset_realCube zone_pos (mel_h _)) (by omega), aliquotMel, firm_real]
 have ht:f i=T*cutM (α i):=by rw [hz]; unfold T; rw [mul_assoc (cutM U),he,←mul_assoc (cutM U),mul_assoc (_*_) (cutM (α i)), (cutM_com ..).eq,mul_assoc (_*_) (cutM V)] -- mul_assoc order
 have hw:‖T‖ ≤ X:=by
    obtain he:= v i w; rw [alf, ←q.caneEq,←t.caneEq,←map_mul,←map_mul,twist_norm] at he; exact he
 rw [ht]; exact cutBudR.trans hw
-- pay.
lemma tenure (h:e≥0)(z:C≥0)(runH:∀ v:Stereo N, v∈Q→ Ream (shineF (stairF 4 (badge v) M)) e C)(p:Hired Q) : ‖R*FrameP Q‖ ≤ C:=by
 let U:= (univ:Finset (Mini N)); have hd:= (show Ballroom U from fun i j _ _ _=> mem_univ _); have he:=hired M h z runH p U U hd hd C z fun i w=> cutBudR.trans (cutBudL.trans ((runH i w).cartLimit N h))
 rw [show cutM U=1 from (by ext i j; by_cases h:i=j <;> simp [cutM,U,h,Matrix.one_apply]),one_mul,mul_one] at he; exact he
lemma vacuum (h:e≥0)(z:C≥0)(runH:∀ v:Stereo N, v∈Q→ Ream (shineF (stairF 4 (badge v) M)) e C)(p:Hired Q):‖cutM (Aeons N (r+d))ᶜ * R * FrameP Q * cutM (Aeons N r)‖ ≤ Real.exp (-e*d)* C:=by
 let U:= cutM (Aeons N r); let L:=Aeons N (r+d); let J:= cutM L; let K:= cutM Lᶜ
 apply hired M h z runH p _ _ ((Ballroom.Awesome _).within_compl) (Ballroom.Awesome _) _ (by positivity); intro i x
 let A:=shineF (stairF 4 (badge i) M); let V:=E₁ A N; let D:=plateH A N d; change ‖K*V*U‖ ≤ _
 have hn: K*D*U=0:=by
    have hl: J*(D*U)=D*U:=(mul_assoc J D U).symm.trans (prolong r d A); rw [mul_assoc,←hl, ←mul_assoc,cutP_com _ _ (subset_refl _) ,zero_mul] -- tune
 rw [← sub_zero (K*V*U), ←hn,←sub_mul,← mul_sub]; exact cutBudR.trans (cutBudL.trans ((runH i x).tollT N h d))
end Curtain
end hprog
end YM.CF.Window.Largo
