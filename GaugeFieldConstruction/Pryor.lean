import GaugeFieldConstruction.Oar
import GaugeFieldConstruction.Gander
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
variable {c f:Side}{M:Male}{Z:Scree.Hub f}{P:BudgetPoint}{Y:InkD f}{d b a C s h:ℝ}{r k:ℕ}{g: Finset (Dwell f)→ℝ}
variable (p:PressB P Z Y h C)(u:Nonwrapping Z.val.2 Z.val.1)(v:∀ i,0≤g i)(dV:∀ U,BedP P U Y Z g)
abbrev Zinc (g:Finset (Dwell f)→ℝ)(x:SM f):= Prism.crack g x.1.1 x.2.1
lemma Zinc_pos(v:∀ i,0≤ g i) (x:SM f) :0≤Zinc g x:= sum_nonneg fun i _=>sum_nonneg fun j _=>v _
lemma Zinc_big(v:∀ i,0≤ g i) (x:SM f) : g (Haro.tray x.1 x.2) ≤ Zinc g x:=by
 let P(i j:SU.Slot):= g (Haro.tray (x.1.1,i) (x.2.1,j));
 apply ((single_le_sum (f:=P x.1.2) (s:=univ) (fun j _=>v _) (mem_univ x.2.2)).trans (single_le_sum (f:=fun i=>∑ j:SU.Slot,P i j) (fun i _=>sum_nonneg fun j _=>v _) (mem_univ _))) -- tune binder
include p u
lemma mast_support {x:tangD f}(F:Fin k→tangD f): SentK Z.val.1 (mastX Y x F):=by
 intro i j v; by_cases h:node i.1.1∈Z.val.2 ∧ node j.1.1 ∈ Z.val.2; · exact ⟨u _ h.1,u _ h.2⟩
 apply False.elim; apply v; unfold mastX; rw [Matrix.of_apply,fadeΩ p i j h]; by_cases q:k=0; · subst k; simp only [iteratedFDeriv_zero_apply]
 rw [iteratedFDeriv_const_of_ne q]; rfl
include dV v
lemma mast_hunt {t:Fin k→ℝ} (F:Fin k→tangD f)(q:∀ i, Lyre.Sized (t i) (F i) P Z.val.1)(h:k ≤P.order): Rode Z.val.1 (∏ i,t i) (Zinc g) (mastX Y 0 F):=by
 refine ⟨mast_support p u F,fun ⟨i,j⟩=> Siete.seals (Prism.sent 1 _ i.1 j.1 (dV 1) (ping_f P _) v i.2 j.2) F t h q⟩ -- tune increment not `sign`: portE.
lemma mast_G1 (x:tangD f)(w:Glass Z x b): Rode Z.val.1 (waist b) (Zinc g) (mastX Y 0 ![x]):=by
 obtain ⟨g,h,T⟩:=w; refine ⟨mast_support p u _,fun i=>?_⟩; rw [mast_Ψ]; exact pay_V_1 p dV v g b T i.1 i.2 x h
lemma mast_G2 (x y:tangD f)(w:Glass Z y b)(gv:Sized a x P Z.val.1):Rode Z.val.1 (strainΦ a b) (Zinc g) (mastX Y 0 ![y,x]):=by rw [mast_v p]; obtain ⟨s,u0,vH⟩:=w; exact ⟨mast_support p u _,fun i=>pay_V_2 p dV v s b vH _ _ _ _ gv u0⟩
-- tide threshold for any short X.B→Jac
structure Stakes (s b:ℝ)(X:Scree.Hub f)(P:BudgetPoint):Prop where
 tA: waist (αSpring P X (s*b)) ≤ b^3
 tB: waist (tideV P X (s*b^2)) ≤ b^3
 tC: strainΦ (4*s*b) (αSpring P X (s*b)) ≤ b^3
variable (q:10 ≤(More f).val)(t:0 ≤ b)(l:b ≤1)(κ:1≤ s)(wZ:Stakes s b Z P) (vM:r=3→landA M Z.val.1 Y P h=0)(gR:r ≤3)
include wZ vM gR q t l κ
lemma mast_middle (x:tangD f)(G:PollenG P Z (s*b^2) x 2)(g₂:Sized (s*b^2) x P Z.val.1): Archive M r Z.val.1 h b (s+2) (Zinc g) (mastX Y 0 ![x]):=by
 have he: Rode Z.val.1 (s*b^2) (Zinc g) (mastX Y 0 ![x]):=by simpa only [Fin.prod_univ_one] using (mast_hunt p u v dV ![x] (t:=fun _=>s*b^2) (by intro i; fin_cases i; exact g₂) ((by decide:1≤6).trans P.order_ge)) -- order vdV
 have hs:0 ≤ s:=by linarith
 have hz:= Zinc_pos v; by_cases hx:r=3; swap
 · have hk:r ≤2:=by omega
   exact (Archive.pay₃ (he.liftH (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one t l hk) hs) hz) t hs hz).weaken (by linarith) t hz -- inference tune
 subst r; obtain ⟨z,h₀,v₀⟩:= G2k u q x G
 let y:=gateC Z.val.1 P.threshold z; let W(i:tangD f):= mastX Y 0 ![i]
 change Glass Z (x-y) _ at v₀; have ht:Rode Z.val.1 _ (Zinc g) (W (x-y)):= mast_G1 p u v dV (x-y) v₀
 have hw(v u:tangD f): W (v-u)=W v-W u:=by
    simp_rw [W,mast_Ψ]; exact (panLinear Y).map_sub v u
 have hm:Rode Z.val.1 ((1:ℝ)*b^3) (Zinc g) (W (x-y)):=ht.liftH (by rw [one_mul]; exact wZ.tB) hz
 have hp:W y=W x-(W (x-y)):=by rw [hw]; abel
 have hh:Rode Z.val.1 ((s+1)*b^(3-need 3)) (Zinc g) (W y):=by
    have hk:= hm.scaleH (-1)
    rw [show W y=W x+-W (x-y) by rw [←sub_eq_add_neg,hp]]; rw [neg_smul,one_smul, norm_neg,norm_one,one_mul] at hk; exact (he.addH hk).liftH (by rw [show 3-need 3=2 from rfl,add_mul]; exact add_le_add_right (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one t l (show 2 ≤ (3:ℕ) from by omega)) zero_le_one) _) hz -- tune
 have hd: quote_B M (W y) Z.val.1 h (need 3):=by refine ⟨fun _=>?_, fun h=> by unfold need at h; omega, fun h=> by unfold need at h; omega⟩; unfold W; rw [mast_Ψ]; exact DFunLike.congr_fun (vM rfl) z
 have hc:=Archive.fuse (Archive.pay₂ hh hd t (by linarith) hz) (Archive.pay₃ (k:=3) hm t zero_le_one hz) -- parse cast `(b:=b)`
 rw [show mastX Y 0 ![x]=W y + W (x-y) from (by rw [hw]; change W x= _; abel)]
 exact hc.weaken (le_of_eq (by ring)) t hz
omit p u v dV wZ vM gR q t l κ
section
lemma sizedι {G H:tangD f}{o:Skye.Seat f}(x:Sized a G P o)(w:Sized b H P o)(T:a+b ≤ s): Sized s (G+H) P o:=by refine ⟨(add_nonneg x.1 w.1).trans T,fun i=>?_⟩; exact (norm_add_le ..).trans ((add_le_add (x.2 i) (w.2 i)).trans ((add_mul ..).symm.le.trans (mul_le_mul_of_nonneg_right T (Lyre.width_pos ..).le)))
lemma sizedMonoι {G:tangD f}{o:Skye.Seat f}(x:Sized a G P o)(T:a ≤ b) : Sized b G P o:=⟨x.1.trans T,fun i=>(x.2 i).trans (mul_le_mul_of_nonneg_right T (Lyre.width_pos ..).le)⟩
end
include p u v dV wZ vM gR q t l κ
lemma swept1 (x:tangD f)(hd:StrongE P Z s b x) : Archive M r Z.val.1 h b (4*s+4) (Zinc g) (mastX Y 0 ![x]):=by -- ‹› fix shadow
 obtain ⟨F,e,W⟩:=hd; let Tq:= Zinc g; have hG:= Zinc_pos v; let P₁:= fun y:tangD f=> mastX Y 0 ![y]; have hp₁(x y):P₁ (x+y) = P₁ x+P₁ y:=by unfold P₁; simp_rw [mast_Ψ]; exact (panLinear Y).map_add _ _
 have hs:0 ≤ s:= zero_le_one.trans κ; let Z':= F 2+F 3; have he:x=F 0+(F 1+Z'):=by unfold Z'; rw [e]; exact Fin.sum_univ_four F|>.trans (by abel)
 have hf:PollenG P Z (s*b) (F 0) 1:=by simpa using (W 0).2 (by decide)
 have hb := mast_G1 p u v dV (F 0) (G1k' u q (F 0) hf)
 have hx:= mast_middle p u v dV q t l κ wZ vM gR (F 1) (show PollenG P Z (s*b^2) _ 2 from (W 1).2 (by decide)) (W 1).1
 have hw:Sized ((2*s)*b^3) Z' P Z.val.1:=by
    refine sizedι ((W 2).1) ((W 3).1) ?_
    change s*b^3+s*b^4 ≤ _ ; linarith only [mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one t l (show 3 ≤ (4:ℕ) by omega)) hs]
 have hy:Rode Z.val.1 (2*s*b^3) Tq (P₁ Z'):=by simpa only [Fin.prod_univ_one] using (mast_hunt p u v dV ![Z'] (t:=fun _=>2*s*b^3) (by intro i; fin_cases i; exact hw) ((by decide:1≤6).trans P.order_ge))
 have hh: Rode Z.val.1 (1*b^r) Tq (P₁ (F 0)):= hb.liftH (by rw [one_mul]; exact wZ.tA.trans (pow_le_pow_of_le_one t l gR)) hG
 change Archive M _ _ _ _ _ _ (P₁ x)
 rw [he,hp₁,hp₁]; exact ((Archive.pay₃ hh t zero_le_one hG).fuse (hx.fuse (Archive.pay₃ (hy.liftH (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one t l gR) (by positivity)) hG) t (by positivity) hG))).weaken (by linarith) t hG
omit vM
include M -- for swept₂
lemma swept₂ (x y:tangD f)(hp:StrongE P Z s b x)(hk:StrongE P Z s b y): Archive M r Z.val.1 h b (16*s^2+1) (Zinc g) (mastX Y 0 ![x,y]):=by
 obtain ⟨F,e,W⟩:=hp; let Tq:= Zinc g; have hG:= Zinc_pos v; let P₂:= fun u:tangD f=> mastX Y 0 ![u,y]
 have hs:0 ≤ s:= zero_le_one.trans κ; let V:= F 1+(F 2+ F 3); have he:x=F 0+V:=by unfold V; rw [e]; exact Fin.sum_univ_four F|>.trans (by abel)
 have hf:PollenG P Z (s*b) (F 0) 1:=by simpa using (W 0).2 (by decide)
 have hv:= G1k' u q (F 0) hf
 have hy:Sized (4*s*b) y P Z.val.1:= payφ _ t l κ (StrongE.tap hk)
 have hb := mast_G2 p u v dV y (F 0) hv hy
 have ht:Sized (4*s*b^2) V P Z.val.1:=by
    have he₂:Sized (2*s*b^2) (F 2+F 3) P Z.val.1:= sizedι (W 2).1 (W 3).1 (by change s*b^3+s*b^4 ≤ _; linarith only [mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one t l (show 2≤ (4:ℕ) from by omega)) hs,mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one t l (show 2 ≤ (3:ℕ) from by omega)) hs]);
    apply sizedι (W 1).1 he₂; change s*b^2+2*s*b^2 ≤ _; linarith only [mul_nonneg hs (sq_nonneg b)]
 have hx:Rode Z.val.1 (16*s^2*b^3) Tq (P₂ V):=by
    let K': Fin 2 → ℝ:= ![4*s*b^2,4*s*b];
    have hx:= mast_hunt p u v dV ![V,y] (t:=K') (by intro i; fin_cases i; exact ht; exact hy) ((by decide:2≤6).trans P.order_ge);
    rw [show ∏ i,K' i=16*s^2*b^3 from (by unfold K'; simp only [Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one]; ring)] at hx; exact hx
 have hm:= hb.addH hx; have he0: (16:ℝ)*s^2≥0:=by positivity
 apply Archive.pay₃ _ t (by positivity) hG; rw [show mastX Y 0 ![x,y]= mastX Y 0 ![F 0,y] + mastX Y 0 ![V,y] from ?_]; swap
 · ext i j; let K:=iteratedFDeriv ℝ 2 (portE Y i j) 0; change K _=K _+K _; rw [show ![x,y]=Function.update ![F 0,y] 0 (F 0+V) from ?_]; swap; · ext1 i; fin_cases i <;> simp [he]
   rw [ContinuousMultilinearMap.map_update_add]; congr 1
 apply hm.liftH _ hG; rw [add_mul,one_mul,add_comm ((16:ℝ)*s^2*_)]
 exact add_le_add (wZ.tC.trans (pow_le_pow_of_le_one t l gR)) (mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one t l gR) he0) -- he shadow! overwritten x def.n

end Boom
end YM.CF.TableF
end
