import YM.SatinExist.Helvet
/-!
 # Strong passage: wave purchase at genuine heights and independence.
-/
set_option autoImplicit false
set_option maxRecDepth 2450
set_option maxHeartbeats 400000
noncomputable section
namespace YM.SatinJets
open Function Filter Metric InnerProductSpace Set Complex MeasureTheory Measure
open Analysis Boundary Spectral OS OS.Semigroup
open CF.Buffered.Afterglow.Hierarchy.Seld Poin LineDeriv
open scoped NNReal ENNReal Topology BigOperators InnerProductSpace ComplexOrder Classical
variable {H : Hilbert}{j:Axis} (S : OS.Semigroup H j)
local notation "Λ" => 𝓝[>] (0:ℝ)
local notation "E" => elast S
local notation "D" => Bench S
local notation "K" => Cache S
local notation "R" => saucer S
local notation "T" => M S
variable (Ω:Bench S)(w:∀ x,M S x Ω.val=Ω.val)
variable {n:ℕ} (F G:Fin n→H.Op)(h:Fin n→ℝ≥0)(f: Fin n→ Test4)
def accord : ∀ {n:ℕ}, (Fin n→ H.Op) → (Fin n → Test4) → D→ₗ[ℂ]D
 | 0,_,_ => LinearMap.id
 | n+1,G,f=> (ℑ₀ S (G 0) (f 0)).comp (accord (Fin.tail G) (Fin.tail f))
def inCourse : ∀ {n:ℕ},(Fin n→ℕ) → (Fin n→H.Op)→ (Fin n→ℝ≥0) → (Fin n → Test4) → D→ₗ[ℂ]D
 | 0,_,_,_,_ => LinearMap.id
 | n+1,l,F,t,f=> (stove S (t 0)).comp ((ℑ S (F 0) (f 0) (l 0)).comp (inCourse (Fin.tail l) (Fin.tail F) (Fin.tail t) (Fin.tail f)))
def pedestal : ∀ {n:ℕ},ℕ → (Fin n→ℕ) → Fin n→ℕ
 | 0,_,_=>Fin.elim0
 | n+1,m,r=> Fin.cons (m+r 0) (pedestal (r 0) (Fin.tail r))
local notation "Ym" f:max=> Joint.materialize _ f
variable (p:E4)
include w
-- external graph prices for all n. Explicit prev displacement
lemma sold (r:Fin n→ℕ)(m:ℕ)(t:∀ i,0<h i): wishL S Ω.val p (slew S (pedestal m r) h) G (Ym f)= T (-p) (hall S m (inCourse S r G h f Ω)):=by
 induction n generalizing p m with
 | zero=>
   rw [wishL_eq]; unfold regia_bill
   rw [Points.volume_nil, integral_dirac]; change Joint.trivial _ • _= T (-p) (hall S m Ω); rw [Joint.trivial_at, one_smul,hallO S Ω (rlock S Ω.val w),w]; rfl
 | succ n ih=>
   let F:=slew S (pedestal m r) h; let A(i):= F i; let V:= fun y=> ((Ym f) y) • regia S Ω.val p F G y -- notation precedence
   rw [wishL_eq]; change (∫ y,V y) = _; rw [Pour V (regiaI ..)]
   let G':=Fin.tail G; let r':= Fin.tail r; let X:= Fin.tail f; let u:=Ω; let H':= Fin.tail h; let z:= r 0
   let x:= (inCourse S r' G' H' X Ω); let W:= hall S z x; let C (q:E4):= T (q-p)*F 0 * G 0
   let Γ:=Fin.tail F; have hv:Γ=slew S (pedestal z r') H':=funext fun i=> by unfold Γ F slew; rw [pedestal]; simp [Fin.tail,r',H',z]
   have he(q:E4)(y:Points n):V (Points.cons q y)= f 0 q • C q ((Ym X) y • regia S Ω.val q Γ G' y):=by
       unfold V; rw [Joint.materialize, Joint.combine_at,mul_smul,map_smul]; change _ • (_ • regiaN S Ω.val (n+1) F G p _) = _; rw [regiaN]; simp only [show WithLp.ofLp (Points.cons q y) 0=q from head_cons ..,show Fin.tail (WithLp.ofLp (Points.cons q y))=WithLp.ofLp y from congrArg (fun p:Points n=> WithLp.ofLp p) (tail_cons q y)]; rfl
   -- simplify external phase then pay interwoven F
   let M(q:E4):= T (-p)* F 0* optx S (G 0) q
   have hp(q:E4): (C q) (T (-q) W)=M q W:= by
       let J(q:E4):= T q; refine DFunLike.congr_fun (?_ : C q* T (-q)=M q) W; unfold M optx C; have ht:q-p= -p+q:=by abel
       rw [ht,← tgo,mul_assoc (T (-p)) (T q) (F 0), ← (show Commute (F 0) (T q) from mslot S q _ (dur.mpr (t 0)) _).eq]; simp_rw [mul_assoc]
   have e(q:E4): (∫ y,V (Points.cons q y)) = f 0 q • M q W:=by
       simp_rw [he,integral_smul, ContinuousLinearMap.integral_comp_comm (C q) (regiaI ..)]; change f 0 q • C q (wishL S Ω.val q Γ G' (Ym X))= _; rw [hv];
       have hw: wishL S Ω.val q _ G' (Ym X)=T (-q) W:= ih _ _ _ q _ z (fun i=>t i.succ); rw [hw,hp]
   rw [show (∫ x:E4,∫ y,V (Points.cons x y)) = ∫ q:E4,f 0 q • M q W from (by simp_rw [e])]
   let S':=T (-p)*F 0
   have he(q): f 0 q • M q W=S' (f 0 q • optx S (G 0) q W) :=by rw [map_smul]; rfl
   let V':= ℑ S (G 0) (f 0) z x
   simp_rw [he,ContinuousLinearMap.integral_comp_comm (S') (emberI ..)]; rw [← vmap]
   change T (-p) (F 0 (valise S (G 0) (f 0) (hall S z x))) = T (-p) (hall S m (stove S (h 0) V'))
   rw [← native, ← priceT]; exact congrArg (T (-p)) (show F 0 (Cache S z V'.val) = _ from DFunLike.congr_fun (Eq.trans (show F 0 *K z=Par S (m+z) (h 0)*K z from rfl) (resolve _ _ m z (t 0))) V'.val) -- price needs h
   exact t 0
omit w
variable (r:Fin n→ℕ)
lemma arrive_on {U:Type*} (ℱ:Filter U)(x: U→ Fin n→ℝ≥0)(y:Fin n→ℝ≥0)(p:Tendsto x ℱ (𝓝 y)): pays_to S ℱ (fun u=> inCourse S r G (x u) f Ω) (inCourse S r G y f Ω):=by
 induction n with
 | zero=> exact fun _=> tendsto_const_nhds
 | succ n ih=>
    let X':= fun (u:U)=> Fin.tail (x u); let t:= Fin.tail y; have e:Tendsto X' ℱ (𝓝 t):= tendsto_pi_nhds.mpr (fun i=> tendsto_pi_nhds.mp p i.succ)
    let A:= G 0; let g:= f 0; let W:= ℑ S A g (r 0); let m:= inCourse S (Fin.tail r) (Fin.tail G) t (Fin.tail f) Ω; have hz := ih (Fin.tail G) (Fin.tail f) (Fin.tail r) X' t e
    simp_rw [inCourse]; exact stoveLim S (y 0) (W m) ℱ _ _ (tendsto_pi_nhds.mp p 0) (ℑLim₁ S A g m (r 0) ℱ _ _ tendsto_const_nhds hz)
include w
lemma computes (Y:Joint n →L[ℂ] H.space)(d:RoadLimit S Ω.val 0 G (pedestal 0 r) Y): Y (Ym f)= (inCourse S r G 0 f Ω).val:=by
 haveI:NeBot (𝓝[Margins n] (0:Fin n→ℝ≥0)):= margin_here
 refine tendsto_nhds_unique (d (Ym f)) ?_
 have e:Tendsto id (𝓝[Margins n] (0:Fin n→ℝ≥0)) (𝓝 0):= tendsto_id.mono_left nhdsWithin_le_nhds; have he:= arrive_on S Ω G f r _ _ _ e
 refine (tune_in S _ _ _ he).congr' ?_
 filter_upwards [self_mem_nhdsWithin] with t z; rw [sold S Ω w G t f 0 r 0 z,neg_zero,tini,CF.Buffered.Afterglow.Hierarchy.Seld.home]; rfl -- order binders
end YM.SatinJets
