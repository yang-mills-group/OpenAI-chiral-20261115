import GaugeFieldConstruction.Victor
/-! Infant Ward estimates at log/link coordinates; site gauge size on exact hub -/
set_option autoImplicit false
set_option maxHeartbeats 45000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.TableF
open Function Filter Metric Lattice Wilson Finset MeasureTheory RG Precision Tree
open Skye Scree
open scoped Topology ContDiff BigOperators InnerProductSpace Matrix MatrixOrder Kronecker Classical -- tune
open FlightFlux Fluxim
open Fock Tulip Lat Spire Phase Cube
open AnalyticBridge VerifiedReset Taxi Lenten Lenten.ModuleB
open Push
open Bank Laurent Bloch Tap Hove Spire
open Haro Hove
open MultiNext.SignedSource PhysicalNext.JointLoad Analysis Siete Banjo
namespace Axon
open SU (E)
open Prism
variable {n:Side}{P: BudgetPoint}{Q: InkD n}{o:Skye.Seat n}{X:Scree.Hub n}{h c s B b V:ℝ}{g:Finset (Dwell n) → ℝ}{m:ℕ}
local notation "αₚ"=> X.val.1
local notation "C'"=> X.val.2
variable (v:PressB P X Q h c)
private abbrev ST (f:Skye.Seat n → SU.group.Color) (x:Rock n):=-(f (node x.1))
abbrev PhiWa (f:Skye.Seat n → SU.group.Color)(x:Rock n)(k:Bool)(i j:SU.Slot):=fderiv ℝ (aull k i j) 0 (ST f x)
abbrev MassWa (f:Skye.Seat n → SU.group.Color)(x y:Rock n)(i l j d:SU.Slot)(z:ℂ):= PhiWa f x true i j * z * aull false l d 0 + aull true i j 0*z * PhiWa f y false l d
abbrev slake (F:InkD n)(x y:Rock n)(i l:SU.Slot):= crib F x y i l ∘ increment 1
lemma pan_port (F:InkD n)(x y:Rock n)(i l:SU.Slot):slake F x y i l=portE F (x,i) (y,l):= rfl -- tune
include v
lemma slake_g (x y:Rock n)(i l:SU.Slot): ContDiffAt ℝ 2 (slake Q x y i l) 0:=by obtain ⟨a,p,P',W⟩:=v.worth; exact (sent 1 a x y (P' 1) (ping_f P _) p i l).paid.of_le (show (2:WithTop ℕ∞) ≤_ from Nat.cast_le.mpr (le_trans (by decide:2≤6) P.order_ge))
lemma PaceG (x y:Rock n)(i l:SU.Slot)(f:Skye.Seat n → SU.group.Color): (fun z=> fderiv ℝ (slake Q x y i l) z (earG f z))=ᶠ[𝓝 0] (fun z=> ∑ d:SU.Slot,∑ j:SU.Slot, MassWa f x y i l j d (slake Q x y j d z)) :=by
 let T:=slake Q x y i l
 have hp(i j k)(b):HasDerivAt (fun t:ℝ=> aull b i j (t • ST f k)) (PhiWa f k b i j) 0:= side _ ((curr ..).differentiable (by simp) 0) _
 have hx: Tendsto (fun z:tangD n=>(z,(0:ℝ))) (𝓝 0) (𝓝 (0:Lift2 SU.group (More n))):= continuousAt_id.prodMk continuousAt_const -- tune
 have ht:∀ᶠ i in 𝓝 (0:Lift2 SU.group (More n)), ContDiffAt ℝ 1 (ChordG f) i:=(chord_K f|>.of_le (m:=1) le_top).eventually (by simp)
 filter_upwards [chord_stand f,hx.eventually ht,hx.eventually (recouped f|>.eventually_nhds), (slake_g v x y i l).eventually (by simp)] with z hu hv hk hT -- tune `.eventually_nhds`
 let G:=fun t:ℝ=> ChordG f (z,t); have ha: HasDerivAt (T ∘ G) (fderiv ℝ T z (earG f z)) 0:= (hT.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt_of_eq 0 ((hv.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0 ((hasDerivAt_const (0:ℝ) z).prodMk (hasDerivAt_id' 0))) hu.symm
 let D(i j):= slake Q x y i j z
 have he := HasDerivAt.fun_sum (u:=univ) (fun (d:SU.Slot) _=> HasDerivAt.fun_sum (u:=univ) (fun (j:SU.Slot) _=> (((hp i j x true).mul_const (D j d)).mul (hp l d y false)))) -- tune binders
 apply ha.unique; apply (HasDerivAt.congr_deriv he ?_).congr_of_eventuallyEq -- tune
 · let p: Tendsto (fun t:ℝ=>(z,t)) (𝓝 0) (𝓝 (z,0)):=continuousAt_const.prodMk continuousAt_id; filter_upwards [p.eventually hk] with t hb
   change crib Q x y i l _= _; rw [show increment 1 (G t) = FlightFlux.Broad f (z,t) from hb]; unfold crib FlightFlux.Broad; rw [forge v, Matrix.mul_apply]; simp only [Matrix.mul_apply,Finset.sum_mul,← smul_neg]; rfl
 · simp only [zero_smul,MassWa,D]
-- along_deriv mixed
lemma CurveWa (f:Skye.Seat n → SU.group.Color)(x y:Rock n)(i l:SU.Slot)(u: tangD n) : iteratedFDeriv ℝ 2 (slake Q x y i l) 0 ![u,VerifiedReset.gradient f] + fderiv ℝ (slake Q x y i l) 0 (strainG f u) = ∑ d:SU.Slot,∑ j:SU.Slot, MassWa f x y i l j d (fderiv ℝ (slake Q x y j d) 0 u):=by
 let T:= slake Q x y i l; let X:= fun t:ℝ=> t • u; let V:= fderiv ℝ T; let E:= earG f; have hx:Tendsto X (𝓝 0) (𝓝 0):=by simpa only [zero_smul] using (show Continuous (fun t:ℝ=> t • u) from continuous_id.smul continuous_const).tendsto (0:ℝ)
 have hp(i l):=slake_g v x y i l
 have hV:ContDiffAt ℝ 1 V 0:=(hp i l).fderiv_right (by decide); have hu: DifferentiableAt ℝ E 0:= earG_d f; let Y:=∑ d:SU.Slot,∑ j:SU.Slot, MassWa f x y i l j d (fderiv ℝ (slake Q x y j d) 0 u);
 have hv(d j:SU.Slot): HasDerivAt (fun t=> MassWa f x y i l j d (slake Q x y j d (X t))) (MassWa f x y i l j d (fderiv ℝ (slake Q x y j d) 0 u)) 0:=by
    let p:= side _ ((hp j d).differentiableAt (by simp)) u; exact ((p.const_mul _).mul_const _).add ((p.const_mul _).mul_const _)
 have hh:HasDerivAt (fun t=> V (X t) (E (X t))) Y 0:=(HasDerivAt.fun_sum fun (d:SU.Slot) _=> HasDerivAt.fun_sum fun (j:SU.Slot) _=> hv d j).congr_of_eventuallyEq (hx.eventually (PaceG v _ _ _ _ _))
 rw [iteratedFDeriv_two_apply]; have he:= ((side _ (hV.differentiableAt (by simp)) u).clm_apply (side _ hu u)).unique hh; simp only [E,zero_smul,earG_0] at he; exact he -- tune
omit v
abbrev waist (t:ℝ):= (Fintype.card SU.Slot:ℝ) * (Fintype.card SU.Slot:ℝ) * (2* Prism.coalT*t)
lemma waist_h : waist B=(waist 1)*B:=by unfold waist; ring
lemma waist_pos(b:ℝ)(h:0≤b):0≤waist b:=by unfold waist; have h:=Prism.coalL; positivity -- tune
lemma standard (i j: Rock n)(p q:SU.Slot)(F:Skye.Seat n → SU.group.Color) (B:ℝ)(hp:‖F (node i.1)‖≤B)(hx:‖F (node j.1)‖≤B) (a: SU.Slot → SU.Slot → ℂ)(g:∀ i j,‖a i j‖≤ V): ‖∑ d:SU.Slot,∑ t:SU.Slot,MassWa F i j p q t d (a t d)‖≤ waist B*V:=by
 let E0:=coalT*B; have hz:0≤ V:= (norm_nonneg _).trans (g p q); have hb:0 ≤ B:=(norm_nonneg _).trans hp; have hU:=coalL; have hV:0 ≤ coalT:=zero_le_one.trans hU; have he:0 ≤ E0:=mul_nonneg hV hb
 have hl(k:Bool)(z:Rock n)(h:‖F (node z.1)‖≤B)(x y): ‖PhiWa F z k x y‖≤ E0:=by unfold PhiWa; apply ((fderiv ℝ _ _).le_opNorm _).trans; exact mul_le_mul (payM ..) (by unfold ST; rw [norm_neg]; exact h) (norm_nonneg _) hV
 let U:=2*E0*V; let s:ℝ:=Fintype.card SU.Slot
 apply (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> s*U) _).trans _); swap
 · unfold waist; rw [sum_const,card_univ,nsmul_eq_mul]; exact le_of_eq (by unfold s U E0; ring)
 intro d _; refine (norm_sum_le ..).trans ((sum_le_sum (g:=fun _=> U) (fun j' _=>?_)).trans (by simp [s]))
 let u:=a j' d; apply (norm_add_le ..).trans; unfold U; rw [norm_mul,norm_mul,norm_mul,norm_mul]; refine (add_le_add (b:= (E0*V)*1) (d:= 1*V*E0) ?_ ?_).trans_eq (by ring); exact mul_le_mul (mul_le_mul (hl true i hp p j') (g _ _) (norm_nonneg u) he) (hus ..) (norm_nonneg _) (by positivity); exact mul_le_mul (mul_le_mul (hus ..) (g _ _) (norm_nonneg u) zero_le_one) (hl false j hx q d) (norm_nonneg _) (by positivity)
private lemma eyeDir {N:Type} [NormedAddCommGroup N][NormedSpace ℝ N]{F:tangD n→N}(p:Signs P o F c){u:tangD n}(k:Lyre.Sized V u P o):‖fderiv ℝ F 0 u‖ ≤ V*c:=by have he:=Siete.seals (k:=1) p (fun _=>u) (fun _=>V) (le_trans (by decide:1≤6) P.order_ge) (fun _=>k); simpa only [iteratedFDeriv_one_apply,Fin.prod_univ_one] using he
lemma port_locus (x y:Single n)(u: Fin m→ tangD n)(f: Fin m→ tangD n)(t:∀ i,Agrees X.val.2 (u i) (f i))(F:tangD n→ℂ)(pF: ∀ x y,Agrees X.val.2 x y→ F x=F y)(g:ContDiffAt ℝ (m:WithTop ℕ∞) F 0) : iteratedFDeriv ℝ m F 0 u= iteratedFDeriv ℝ m F 0 f:=by
 let Z:= Mom.screen (G:=SU.group) X.val.2; have he: F ∘ Z= F:=by funext i; exact pF _ _ fun j v p=> by unfold Z; rw [Mom.screen_at, if_pos ⟨v,p⟩]
 have hx (u:Fin m→ tangD n): iteratedFDeriv ℝ m F 0 u= iteratedFDeriv ℝ m F 0 (fun i=> Z (u i)):=by
    have h:= Next.Foundations.jets_linear Z g; rw [he] at h; exact DFunLike.congr_fun h u
 have hf: (fun i=> Z (u i))= fun i=> Z (f i):=by
    funext i j; unfold Z; rw [Mom.screen_at,Mom.screen_at]; by_cases h: Mom.needed X.val.2 j; · rw [if_pos h,if_pos h,t i j h.1 h.2]
    rw [if_neg h,if_neg h] -- indentation tune
 exact (hx u).trans ((congrArg (fun p=> iteratedFDeriv ℝ m F 0 p) hf).trans (hx f).symm)
include v
lemma booth (x y:Rock n)(i j:SU.Slot)(p q:tangD n)(g:Agrees X.val.2 p q): slake Q x y i j p=slake Q x y i j q:=by
 have he:=v.term (increment 1 p) (increment 1 q) (fun k v w=> congrArg (fun z=> SU.group.lieExp z * (1:Pane n) k) (g k v w)); unfold slake crib; simp only [Function.comp_apply,he]
lemma fadeΩ (x y:Single n)(H:¬(node x.1.1∈X.val.2 ∧ node y.1.1∈X.val.2)): portE Q x y =(fun _=> 0):=by
 funext i; unfold portE orbitPH; rw [Matrix.of_apply,port_eq]; split; rfl; change _* Pastry.crumb _ (tray x y)= _; rw [Pastry.Flour.door (v.fitted _) (T:=tray x y),mul_zero]; intro j; let W:= Finset.mem_powerset.mp (Finset.mem_filter.mp j).1; exact H ⟨(mem_filter.mp (W (show (true,x)∈tray x y from by simp [Haro.tray]))).2,(mem_filter.mp (W (show (false,y)∈tray x y from by simp [Haro.tray]))).2⟩ -- tune names
lemma booth_grad (x y:Rock n)(i j:SU.Slot)(p q:tangD n)(g:Agrees X.val.2 p q): fderiv ℝ (slake Q x y i j) 0 p=fderiv ℝ (slake Q x y i j) 0 q:=by simpa only [iteratedFDeriv_one_apply] using port_locus (m:=1) (X:=X) (x,i) (y,j) (fun _=> p) (fun _=> q) (fun _=>g) (slake Q x y i j) (booth v _ _ _ _) ((slake_g v _ _ _ _).of_le (by decide)) -- tune natcast
variable (p:∀ U, BedP P U Q X g) (H:∀ i,0 ≤ g i) (s:Skye.Seat n→ SU.group.Color)(b:ℝ)(hV:∀ i∈X.val.2,‖s i‖≤ b)
include p H hV
lemma pay_V_1 (i j:Single n)(u: tangD n)(w: Agrees X.val.2 u (VerifiedReset.gradient s)): ‖fderiv ℝ (portE Q i j) 0 u‖ ≤ waist b*crack g i.1 j.1:=by
 let F:=slake Q i.1 j.1 i.2 j.2; have he:F=portE Q i j:=rfl
 by_cases h:node i.1.1∈ X.val.2 ∧ node j.1.1∈ X.val.2; swap
 · rw [fadeΩ v i j h,fderiv_fun_const]; change ‖(0:ℂ)‖ ≤ _; rw [norm_zero]; exact mul_nonneg (waist_pos _ ((norm_nonneg _).trans (hV _ X.property))) (Prism.sent 1 _ _ _ (p _) (ping_f P X.val.2) H i.2 j.2).grade
 have hu:= (PaceG v i.1 j.1 i.2 j.2 s).eq_of_nhds; rw [earG_0] at hu; change ‖fderiv ℝ (slake Q _ _ _ _) 0 u‖ ≤ _; rw [booth_grad v _ _ _ _ u _ w,hu]; apply standard i.1 j.1 i.2 j.2 _ b (hV _ h.1) (hV _ h.2) ; exact fun i' j'=> (Prism.sig0 (Prism.sent 1 _ i.1 j.1 (p _) (ping_f P X.val.2) H i' j'))
abbrev strainΦ (V b:ℝ):= waist b* V + ScoreWa SU.group*b*V
lemma pay_V_2 (i j:Single n)(u x:tangD n)(k:Lyre.Sized V x P αₚ)(w:Agrees X.val.2 u (VerifiedReset.gradient s)): ‖mastX Q 0 ![x,u] i j‖≤ strainΦ V b *crack g i.1 j.1:=by
 let F:=slake Q i.1 j.1 i.2 j.2; let Y:=crack g i.1 j.1; have hx(i' j'): Signs P αₚ (slake Q i.1 j.1 i' j') Y := Prism.sent 1 g i.1 j.1 (p _) (ping_f P X.val.2) H i' j'
 have ht:0 ≤ b:= (norm_nonneg _).trans (hV _ X.property)
 by_cases e:node i.1.1∈ X.val.2 ∧ node j.1.1∈ X.val.2; swap
 · rw [mastX,Matrix.of_apply,fadeΩ v i j e,iteratedFDeriv_const_of_ne (by decide)]; let h:=hx i.2 j.2; change ‖(0:ℂ)‖≤ _; rw [norm_zero]; exact mul_nonneg (add_nonneg (mul_nonneg (waist_pos _ ht) k.1) (mul_nonneg (mul_nonneg ScoreWa_pos ht) k.1)) h.grade
 let h:= hx i.2 j.2
 have ha(a:Fin 2):Agrees X.val.2 (![x,u] a) (![x,VerifiedReset.gradient s] a):=by fin_cases a; exact fun _ _ _=>rfl; exact w
 have hy:= port_locus i j _ _ ha F (booth v i.1 j.1 i.2 j.2) ((slake_g v i.1 j.1 i.2 j.2).of_le (by decide)) -- tune booth
 let S:=strainG s x; have hf: Agrees X.val.2 S (Mom.screen X.val.2 S):=fun i a b=>by rw [Mom.screen_at,if_pos ⟨a,b⟩]
 have hg: ‖fderiv ℝ F 0 S‖≤ ScoreWa SU.group*b*V*Y:=by unfold F; rw [booth_grad v _ _ _ _ S _ hf]; exact eyeDir (F:=F) h (strain_pay s V b P C' αₚ ht hV k)
 have hu:= standard i.1 j.1 i.2 j.2 s b (hV _ e.1) (hV _ e.2) _ (fun t q=> eyeDir (hx t q) k)
 have hC:= CurveWa v s i.1 j.1 i.2 j.2 x
 change ‖iteratedFDeriv ℝ 2 F 0 _‖ ≤ _; rw [hy, show iteratedFDeriv ℝ 2 F 0 _ = _ from eq_sub_of_add_eq hC]; exact (norm_sub_le ..).trans ((add_le_add hu hg).trans_eq (by unfold strainΦ; ring)) -- tune
end Axon
end YM.CF.TableF
end
