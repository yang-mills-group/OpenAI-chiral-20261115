import GaugeFieldConstruction.Energy
set_option autoImplicit false
set_option maxHeartbeats 50000
set_option quotPrecheck false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical Matrix.Norms.L2Operator
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
attribute [local instance] opCStarAlgebra
open AnalyticBridge VerifiedReset Taxi
open Lenten
open Stationary Vault Font
open Bank Laurent Bloch Tap Hove Spire
open Haro Peaks Rush Fir Next.Free Thorn
open Planned.PrimaryIntegral295 Carrier
namespace Boom
open TableF.Axon Siete Lenten.ModuleB MultiNext.SignedSource Lyre Banjo Analysis
variable {c f:Side}{M:Male}{Z:Scree.Hub f}{P:BudgetPoint}{d b a C s h:ℝ}{r k m:ℕ}{g: Finset (Dwell f)→ℝ}{Q H:Op (Single f)}{X:SM f→ℝ}{p:BudgetPoint}
lemma ζcred (v:∀ i,0≤g i)(u:p.power=3)(e:0≤h)(o:Skye.Seat f) : h^2*WhX 3 (Zinc g) o ≤ Haro.flavor^2*Hake.joinV (Scree.tariff p o h) g:=by
 rw [← Wh_charge p u]; let V:=Prism.crack g; refine le_trans (b:=flavor^2*(∑ i:Prism.Rock f,∑ j:Prism.Rock f, Haro.amt p.power o i j*h^2* V i j)) (le_of_eq ?_) (mul_le_mul_of_nonneg_left (pay_j g h o v e) (sq_nonneg _))
 let S(a b:Single f):= Zinc g (a,b)*Scree.tariff p o h (tray a b)
 change (∑ i:Single f× Single f, S i.1 i.2)= _; rw [Fintype.sum_prod_type,Fintype.sum_prod_type, Finset.mul_sum]; apply sum_congr rfl; intro i _; simp_rw [show ∀ b:SU.Slot,(∑ j:Single f,S (i,b) j)= ∑ l:Prism.Rock f,∑ v:SU.Slot,S (i,b) (l,v) from fun _=> Fintype.sum_prod_type _]; rw [sum_comm,mul_sum]
 apply sum_congr rfl; intro j _; change (∑ x:SU.Slot,∑ y:SU.Slot,S (i,x) (j,y))=_; rw [show (∑ x:SU.Slot,∑ y:SU.Slot,S (i,x) (j,y))=(∑ a:SU.Slot,∑ b:SU.Slot,V i j*(amt p.power o i j*h^2)) from ?_]; swap
 · refine sum_congr rfl fun a _=> sum_congr rfl fun b _=>?_
   change V i j*tariff p o h (Haro.tray (i,a) (j,b))= _; exact congrArg (fun x=> V i j*x) (Haro.rope p.power o i j a b h p rfl)
 simp only [sum_const,card_univ,nsmul_eq_mul,flavor]; ring
variable {G:Ratio c f}{σ U B:Bool→ℝ}{T:Script Male}{e:Odd G.count.val}{o:Skye.Seat f}
lemma tot_add(E F:Op (Single f))(m:Male)(k:ℕ):totF k G e T m (E+F)=totF k G e T m E+totF k G e T m F:=by unfold totF; simp only [mul_add, add_mul, Matrix.mul_add, Matrix.add_mul]
lemma tot_scale(E:Op (Single f))(m:Male)(k:ℕ)(a:ℝ):totF k G e T m (a • E)=a • totF k G e T m E:=by unfold totF; simp only [Matrix.mul_smul,Matrix.smul_mul]
variable (α:Silks σ U B m)(u:3 ≤ m)(he:Use 4 G.count T)(v:100 < f.val)(dT:h≠0)
include e α u he v dT
lemma pull_one (p:Rode o a X Q)(k':r ≤3)(g:quote_B M Q o h r)(hx:0 ≤a)(hC:∀ i,0 ≤X i)(x:SM c): ‖totF 4 G e T M Q x.1 x.2‖≤ a*Γrep G M o X r x:=by
 by_cases h:a=0
 · have he':Q=0:=Matrix.ext fun i j => norm_le_zero_iff.mp (le_trans (p.cost (i,j)) (by rw [h, zero_mul])) -- type?
   rw [he',h,zero_mul]; unfold totF; simp
 let Q':=a⁻¹ • Q; have hA:p=p:= rfl; let P':=p.scaleH a⁻¹; have hU:‖a⁻¹‖ * a=1:=by rw [Real.norm_of_nonneg (inv_nonneg.mpr hx), inv_mul_cancel₀ h]
 have hp' :∀ i:SM f,‖Q' i.1 i.2‖≤ X i:= fun i=> (P'.cost i).trans (by rw [hU,one_mul]); have ht:= RemAni α u e hC P'.sent (quote_scale g _) v k' dT hp' he x
 let V:=totF 4 G e T M Q'; let i:=x.1; let j:=x.2; rw [show Q=a • Q' from (smul_inv_smul₀ h Q).symm, tot_scale]; change ‖a • V i j‖≤ _; rw [norm_smul,Real.norm_of_nonneg hx]; exact mul_le_mul_of_nonneg_left ht hx
omit v dT he e α u
lemma score_GR(G:Ratio c f)(B:Bool→ℝ)(r:ℕ): ScoreBB B G r=ScoreBB B G 0*(αN G.count)^r:=by unfold ScoreBB wageX; rw [pow_zero,mul_one]; ring
abbrev LanceZ(G:Ratio c f)(M:Male)(o:Skye.Seat f)(C:ℝ)(X:SM f→ℝ)(r:ℕ)(i:SM c):= C*Γrep G M o X r i+C*αN G.count^(r-need r)*Γrep G M o X (need r) i+C*αN G.count^r*Γrep G M o X 0 i
include v dT he e α u
lemma pull_v (p:Archive M r o h (αN G.count) C X Q)(cV:0≤C)(hX:∀ i,0≤X i)(u₀:r≤3)(i:SM c):‖totF 4 G e T M Q i.1 i.2‖≤ LanceZ G M o C X r i:=by
 obtain ⟨U,V,W,h,h',x,y,u',g⟩:=p.bill; rw [h,tot_add,tot_add,Matrix.add_apply,Matrix.add_apply]; have ht:=α_pos G.count
 exact (norm_add_le ..).trans ((add_le_add ((norm_add_le ..).trans (add_le_add (pull_one α u he v dT (e:=e) h' u₀ u' cV hX i) (pull_one α u he v dT (e:=e) x (by unfold need; omega) g (by positivity) hX i))) (pull_one (r:=0) α u he v dT (M:=M) (e:=e) y (by omega) (show quote_B M W _ _ 0 from ⟨fun h=>by omega,fun h=>by omega,fun h=>by omega⟩) (by positivity) hX i)))
omit v dT he
lemma Lance_cost (cV:0≤C)(hX:∀ i,0≤X i)(u₀:r≤3)(o:Skye.Seat f) : (∀ i,0≤LanceZ G M o C X r i) ∧ WhX 3 (LanceZ G M o C X r) (downT G o) ≤ (3*C)*ScoreBB B G r*WhX 3 X o :=by
 let V(i:ℕ):= Γrep G M o X i; have hh(i:ℕ)(p:i≤3):= MajorV α u e hX p o M
 let z:= αN G.count; have hp:0 ≤ z:= (α_pos G.count).le; have ht: need r ≤ r:= Nat.sub_le ..; have h₀:=ht.trans u₀
 let o':= downT G o
 have hk(a): 0 ≤ C*z^(a:ℕ):=by positivity
 let U:=LanceZ G M o C X r; refine ⟨fun i=> add_nonneg (add_nonneg (mul_nonneg cV ((hh r u₀).1 i)) (mul_nonneg (hk (r-need r)) ((hh (need r) h₀).1 i))) (mul_nonneg (hk r) ((hh 0 (by omega)).1 i)),?_⟩
 let Wr:=WhX 3 X o
 have he(k:ℕ)(p:k≤r): C*z^(r-k)*WhX 3 (V k) o' ≤ C*ScoreBB B G r * Wr:= by apply (mul_le_mul_of_nonneg_left (hh k (p.trans u₀)).2 (hk _)).trans_eq; rw [score_GR G B r, score_GR G B k]; unfold z Wr; rw [show αN G.count^r=αN G.count^k *αN G.count^(r-k) from (by rw [←pow_add, Nat.add_sub_of_le p])]; ring -- score_GR if k=0 dec? rewrite caution
 rw [show WhX 3 (LanceZ G M o C X r) o'= C*WhX 3 (V r) o'+C*z^(r-need r)*WhX 3 (V (need r)) o'+ C*z^r*WhX 3 (V 0) o' from (by unfold WhX V LanceZ; simp only [mul_add,sum_add_distrib,mul_sum]; unfold z; congr 1 <;> first | (apply congrArg₂ (·+·) <;> apply sum_congr rfl <;> intros <;> ring) | (apply sum_congr rfl; intros; ring))]
 have ha:=he r (le_refl r); rw [Nat.sub_self,pow_zero,mul_one] at ha; exact (add_le_add (add_le_add ha (he _ ht)) (he 0 (Nat.zero_le r))).trans_eq (by unfold Wr; ring)
end Boom
end YM.CF.TableF
end
