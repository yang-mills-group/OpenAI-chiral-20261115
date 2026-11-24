import YM.SU5.WakeFields.Cesto
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option maxHeartbeats 280000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Resolving.FootLights
open Function Filter Metric Cube Lat Lattice Satin Fock Finset MeasureTheory
open scoped Topology BigOperators Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace ComplexOrder Classical
open Py Py.Rate LocalLimit FullBill Preparation Yoke Yoke.Shuttle
open Lifted EmberWind EmberWind.Staff EmberWind.MixedCards MixedCards.Receipt
open Papal (household)
open Regis.Head.Brecht Regis.Circuit
open Ballad
open Tapestry Journey Heat
open Jewel
open YM.Stationary (Gaia)
open YM.WakeFields
attribute [local instance] opCStarAlgebra
local notation "z" => (3:Axis)
local notation "Kc" => P.calibration
variable {J:Type*}[Fintype J](L:List J)(u:ℕ → J→ Cover)(D:J→MixedCards.Ticket)(P:Spine)
variable (r:ℕ)(n:ℕ)(m:4≤r) {β:ℕ→ℝ}(f:ℕ→ℕ)(V:Tuned P f β){A:ℝ}(p:0<A)
variable {K:P.Register}{M:ℕ}{E:ℝ}(X:Spine.PreparedInvestment P K E M)
variable (U:J→ Gaia)(t:∀ i,Appoint P.par A (fun s=>u s i) (U i)) (hp:∀ i j,U i=U j→∀ᶠ s in atTop,u s i=u s j)(w:L.Pairwise (fun i j=> U i≠U j))
local notation "ω" s:max x:max=> letterTest L D P s r (κFix β s) A m x
local notation "Ua" i:max=> Rosters U U P.par i
local notation "Uc" => Sum.elim D D
local notation "W_" i:max=> plaque (twins L) (Sum.elim D D) (Ua i)
local notation "W₀"=> plaque L D U
local notation "S₀" s:max=> studioR P s
include V X p t hp w
lemma joinage (L':List (J⊕J))(n:ℕ)(l:L'.Pairwise (fun i j=> (Ua n) i ≠ (Ua n) j))(g:∀ i, 0 < (pathUp U P.par n i) (3:Axis)) : Tendsto (fun s:ℕ=> (S₀ s) (letterTest L' (Sum.elim D D) P s r (κFix β s) A m (troupe (u s) P.par A n s))) atTop (𝓝 (plaque L' (Sum.elim D D) (Ua n))) := by
  obtain ⟨k,h⟩:= troupe_loan p t hp n g
  exact (paidAdjacents P L' (Sum.elim D D) f V p X (fun _=>primary) (fun _=> Spine.pairMood) (Ua n) (fun s=> troupe (u s) _ A n s) k h r m l).realized
lemma spectrum0rev : Tendsto (fun s:ℕ=> (S₀ s) (ω s (u s))) atTop (𝓝 W₀) := (paidAdjacents P L D f V p X _ _ U u t hp r m w).realized
-- phase transpose of plaque -- price along Shuttle.flip alone and use actual E.
include m
lemma reversible : plaque L D (opposite ∘ U)=star (plaque L D U):=by
  let a:J→ Gaia:=opposite∘U; let F (s:ℕ):= Shuttle.flip ∘ u s
  have he: Tendsto (fun s:ℕ=> (S₀ s) (ω s (F s))) atTop (𝓝 (plaque L D a)):= (paidAdjacents P L D f V p X _ _ a F (fun i=> xflip_a (t i)) (fun i j e=> (hp i j (flip_inj e)).mono fun i h=> congrArg Shuttle.flip h) r m (w.imp fun x=> flip_inj.ne x)).realized
  apply tendsto_nhds_unique he
  have hx := (spectrum0rev L u D P r m f V p X U t hp w).star
  apply hx.congr; intro s
  let B := ω s (u s)
  have h: P.reflectTest 3 B=ω s (F s):= Subtype.ext (stampReflection ..)
  change star ((S₀ s) B) = _; rw [←mirror_phase,h]

lemma father_bill (n:ℕ)(g:∀ i,0< (pathUp U P.par n i) z) : let G (s):= P.halfShift 3 (kroll P.par A n s) (ω s (u s)); Tendsto (fun s=> (S₀ s) (P.reflectTest 3 (G s) * G s)) atTop (𝓝 (W_ n)) := by
  intro G
  have he(i j:J)(q:U i≠U j) : pathUp U P.par n i ≠ pathUp U P.par n j:=fun e=> q (add_right_cancel e)
  have hn:L.Pairwise (fun i j=>pathUp U P.par n i ≠ pathUp U P.par n j):= w.imp (fun h=> he _ _ h)
  have hp₀: (twins L).Pairwise (fun i j=> (Ua n) i ≠ (Ua n) j):=by
    refine List.pairwise_append.mpr ⟨List.pairwise_map.mpr ?_, List.pairwise_map.mpr hn,?_⟩
    · exact hn.imp fun p=> flip_inj.ne p
    rintro i I j J; obtain ⟨i,p,rfl⟩:=List.mem_map.mp I; obtain ⟨j,b,rfl⟩:=List.mem_map.mp J; intro l; have h:= congrArg (fun t:Gaia=>t 3) l; change opposite _ z = (pathUp U P.par n j) z at h; rw [opp_tim] at h; exact (ne_of_lt ((neg_lt_zero.mpr (g i)).trans (g j))) h
  apply (joinage L u D P r m f V p X U t hp w (twins L) n hp₀ g).congr
  intro s; apply congrArg ((S₀ s)); apply Subtype.ext; exact (mirror_set L (u s) D P s r (κFix β s) A n).symm

omit V X p t hp w m

def earnings(s:ℕ) : P.Test →ₗ[ℂ] ℂ where
 toFun:= studioR P s
 map_add' f g:= E_add P.run P.large P.law s f.property g.property
 map_smul' c f:= E_scale P.run P.large P.law s f.property c
lemma receiptP (s:ℕ)(u:P.Test)(q:ℂ) :
 let S:= S₀ s; let u':= u-q• (1:P.Test)
 S (P.reflectTest z u' * u') = S (P.reflectTest z u*u)- q*star (S u)- star q*S u+ star q*q:=by
 intro S u'; let e:= earnings P s; let F:= P.reflectTest z
 have he:F u'*u'= F u*u-q • F u-star q • u+ (star q*q) • (1:P.Test):=by
    rw [show u'=u-q • 1 from rfl, map_sub, LinearMap.map_smulₛₗ]; rw [show F 1=1 from aureoleUnit ..];
    simp only [starRingEnd_apply,mul_sub,sub_mul,Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_sub,smul_smul,mul_comm q (star q),mul_one,one_mul]; abel
 change e (F u'*u')= e (F u*u)-q*star (e u)- star q*e u+ star q*q; rw [he,map_add,map_sub,map_sub, map_smul,map_smul,map_smul,smul_eq_mul,smul_eq_mul, smul_eq_mul, show e 1=1 from E_unit P.run P.large P.law s, mul_one, show e (F u)= star (e u) from (mirror_phase P s u)] -- E_unit implicit

include V X p t hp w
include m
lemma paid_while (n:ℕ)(g:∀ i, 0<(pathUp U P.par n i) z):
    let v(s):= P.halfShift 3 (kroll P.par A n s) (ω s (u s)); let G (s):= v s- W₀ • (1:P.Test)
    Tendsto (fun s=> (S₀ s) (P.reflectTest z (G s)*G s)) atTop (𝓝 (W_ n-star W₀ * W₀ )):=by
  intro v G; let J₁(s):= ω s (u s)
  have he(s) : (S₀ s) (v s)= (S₀ s) (J₁ s):=letter_revenue ..
  have ht:=father_bill L u D P r m f V p X U t hp w n g; let Q:= W_ n; let H:= W₀;
  have hv : Tendsto (fun s:ℕ=> (S₀ s) (v s)) atTop (𝓝 W₀):= (spectrum0rev L u D P r m f V p X U t hp w).congr fun s=>(he s).symm
  have h:= ((ht.sub (hv.star.const_mul (W₀))).sub (hv.const_mul (star W₀))).add_const (star W₀* W₀); rw [show Q-H*star H-star H*H+star H*H=Q-star H*H by ring] at h; exact h.congr fun s=> (receiptP ..).symm

omit V X hp w
include p t
lemma before_wing (n:ℕ)(g:∀ i, 0<(pathUp U P.par n i) z)(x:ℂ)(β:ℕ→ℝ) :
    ∀ᶠ s:ℕ in atTop, let v:= P.halfShift 3 (kroll P.par A n s) (letterTest L D P s r (κFix β s) A m (u s)); let S:=forward (u s) P.par A n s; let G:=paperX L S r
      InTest P.calibration true G false (v-x • 1).val ∧ Tower.region z 0 P.calibration.ℓ G:=by
  have hq := eventually_all.mpr fun i=> xfront p (xplus_a p (t i) n) (g i) (P.calibration.ℓ+(r+8))
  filter_upwards [hq] with s p v S Q; let K:=letterTest L D P s r (κFix β s) A m S; rw [show v=K from letter_roll ..]
  refine ⟨Tower.InTest.subOp (paperBook L S D P _ _ _ _ m).1 (.smul x .one),paper_room L S P r (fun i _=>?_)⟩
  specialize p i; exact Nat.cast_add (R:=ℤ) _ _ ▸ p

-- Variance
include V X hp w
lemma paysPoll : Spine.WakePoll P (fun s=> ω s (u s)) W₀:= by
 let Φ (s):= ω s (u s); let T:= W₀
 have hg:Tendsto (fun n=> W_ n) atTop (𝓝 (star W₀* W₀)):= reversible L u D P r m f V p X U t hp w ▸ (tariffs_unroll L D U P.par D U L)
 constructor; intro c hc; obtain ⟨n,p₀,f₀⟩:= ((Metric.tendsto_nhds.mp hg c hc).and (Filter.eventually_all.mpr (fun i=> (gait_up P.par (U i)).eventually_gt_atTop 0))).exists
 rw [dist_eq_norm] at p₀
 filter_upwards [(paid_while L u D P r m f V p X U t hp w n f₀).norm.eventually (gt_mem_nhds p₀), before_wing L u D P r m p U t n f₀ T β] with s h u₁;
 let v := P.halfShift z (kroll P.par A n s) (Φ s); let x:= v-T • (1:P.Test);
 have hn (a:P.Spectrum0 z) : P.singleState z s a (ω s (u s))- W₀=P.singleState z s a x:=by
    unfold x; rw [map_sub,map_smul,P.single_state z s a v, show P.singleState z s a 1=1 by simp [Spine.single_state]]; unfold v; rw [P.halfReads]; simp only [smul_eq_mul,mul_one]; rfl
 simp_rw [hn]; exact lt_of_le_of_lt (reimburse P s x _ u₁.1 u₁.2) h

#print axioms joinage
#print axioms reversible
#print axioms receiptP
#print axioms before_wing
#print axioms paysPoll
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection.Resolving.FootLights
