import YM.CF.Rue.Pace
import YM.CF.Cloak.Flux
import YM.CF.Forge.Seal
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option quotPrecheck false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Rue
open Function NormedSpace Filter Metric Lattice Wilson Laurent Finset Cube SU Fock Lat Spire Scroll MeasureTheory Mesa ProbabilityTheory Peaks Drapes Rush Precision Tree Push.SectorMeasure Next.SectorChange Tulip Jet Tap Laic Dial Paige Vault Pec Skye Pastry Cascade Scree
open scoped Topology ContDiff BigOperators InnerProductSpace ComplexConjugate NNReal ENNReal Matrix MatrixOrder Kronecker Classical Matrix.Norms.Frobenius
open RG Pressure
open Forge Pressure.Tube CF.Esti CF.Cloak CF.Rill CF.Jet
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{p v s C c a:ℝ}{n:ℕ}
local notation "G₀"=> SU.group
local notation "D"=> SU.group.colorScale
def padK(F:E→SU.E)(q:Chi)(s:ℝ)(i:E):ℝ:=q.read ((SU.group.chord (F i)/(s/2))^4)
lemma padHi(F:E→SU.E)(q:Chi)(u:0<s)(l:x∈tsupport (padK F q s))(g:ContinuousAt F x):SU.group.chord (F x)< s:=by
 let W(x):= (SU.group.chord (F x)/(s/2))^4
 have h:ContinuousAt W x:=by refine (ContinuousAt.div_const ?_ _).pow _; exact SU.group.continuous_chord.continuousAt.comp g
 by_contra! z; have ht:2 ≤ SU.group.chord (F x)/(s/2):=(le_div_iff₀ (by positivity : (0:ℝ)<s/2)).mpr (by linarith only [z]); have he:4 < W x:= LT.lt.trans_le (by norm_num : (4:ℝ)<2^4) (pow_le_pow_left₀ zero_le_two ht _)
 have hz:∀ᶠ v in 𝓝 x,padK F q s v=0:= (h.eventually (lt_mem_nhds he)).mono (fun i p=> q.to_zero _ p.le)
 exact (notMem_tsupport_iff_eventuallyEq.mpr hz) l
lemma e_cont(V:E→SU.E)(u:Tender V x s n):ContinuousAt V x:=(SU.group.continuous_mat.isClosedEmbedding SU.group.mat_injective).isEmbedding.tendsto_nhds_iff.mpr u.smooth.continuousAt
lemma mantle(q:Chi)(n:ℕ)(p:D≤C) : ∃ W:ℝ,0 ≤ W ∧ ∀ {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E]{x:E}{s:ℝ},0<s →∀ F:E→ SU.E, Tender F x (C*s) n → Allows n (padK F q s) x W:=by
 obtain ⟨v,w,h⟩:= Esti.cost_χ q true n; let M:=D⁻¹*C; let Z:ℝ:= (2:ℝ)^n*M*M; let L:=16* ((2:ℝ)^n* ‖ContinuousLinearMap.mul ℝ ℝ‖*Z*Z); let K:=composeCost n v L; have hz:=SU.group.colorScale_pos; have ht:= hz.trans_le p; have hk:0≤K:=by unfold K L Z M composeCost; positivity
 refine ⟨K,hk,@fun E _ _ x s l F g=>?_⟩; by_cases v': x∈tsupport (padK F q s); swap; · exact (allows_const _ (by simpa only [norm_zero] using hk: ‖(0:ℝ)‖≤ K)).germ (EventuallyEq.symm (notMem_tsupport_iff_eventuallyEq.mp v'))
 let H(y):= (SU.group.chord (F y)/s)^2; have hm: Allows n H x Z:= Cloak.white _ l F g (padHi F q l v' (e_cont F g)).le p
 have he:Allows n (fun x=> (SU.group.chord (F x)/(s/2))^4) x L:=by
    apply ((hm.bilinear (ContinuousLinearMap.mul ℝ ℝ) hm le_rfl).smul 16).mono (show |(16:ℝ)| *_=L from by rw [abs_of_nonneg]; norm_num).le |>.germ
    refine Eventually.of_forall fun x=>?_ ; change 16*(H x*H x)=(SU.group.chord (F x)/(s/2))^4; unfold H; ring
 exact (h _).comp he -- tune proof cost norm matrix l₂ instances G lean
open MultiNext.SignedSource Lyre
variable {m:Side}{W:Support (More m)}{P:BudgetPoint}{I:Finset (Bond (More m))}{U:E→Pane m}{o:Hub m}{F:Pane m→ ℂ}
lemma graftP (C:ℝ)(n:ℕ) (hp:0≤C):∃ t Z:ℝ, 0<t ∧ 1≤Z ∧∀{m:Side}{H:BudgetPoint}(o:Hub m), H.order=n→ H.threshold ≤ t →∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](V:E→ Pane m)(x:E)(I: Finset (Bond (More m))), (∀ j:Bond (More m),Skye.ends j⊆ o.val.2 → Tender (fun y=> V y j) x (C*H.threshold) n) → (∀ j:Bond (More m),Skye.ends j⊆o.val.2 → j∉I → ∀ᶠ y in 𝓝 x,V y j=V x j) →∀ (Ψ: Pane m→ℂ)(K:ℝ), LocalOn o.val.2 Ψ→ Signs H o.val.1 (Ψ ∘ gyrate I (V x)) K→ Allows n (Ψ ∘ V) x (Z*K):=by
 obtain ⟨d,B,g,h,t⟩:=Rill.ank n; let z:=d/(C+1); have hz:0<z:=by unfold z; positivity
 let F:= fun a:ℝ=>composeCost n a (B*C); let T':=F 1; refine ⟨z,max T' 1,hz,le_max_right ..,fun {m H} o L v E _ _ V x I r p U K q hK =>?_⟩; let e:=H.threshold; have he:0<e:=H.threshold_pos
 let P(t:E)(j:Bond (More m)):= if Skye.ends j⊆o.val.2 then LocalH.snap G₀ (V t j*(V x j)⁻¹) else 0
 let H'(u):=gyrate I (V x) (P u); let k:E→ tangD m:=Prism.silo H o.val.1 ∘ P
 have hp':0 ≤ B:=zero_le_one.trans h; have hv:B*C*e/e=B*C:= by field_simp
 have hr:C*H.threshold ≤ d:=((mul_le_mul_of_nonneg_left v hp).trans (by unfold z; field_simp; linarith only [g]))
 have hc:∀ j:Bond (More m),Skye.ends j⊆ o.val.2  → ContinuousAt (fun y=>V y j) x:=fun j v=> e_cont _ (r j v) -- tune
 have hh(j):P x j=0:=by unfold P; split; exact congrArg Prod.fst (fleck (V x j,(1:SU.E))).1; rfl
 have hP(j):Allows n (fun x=>k x j) x (B*C):=by
    let v:= Lyre.width H o.val.1 j
    have hx:e ≤ v:=le_mul_of_one_le_right he.le (one_le_pow₀ (by simp))
    have hp(j:Bond (More m)):Allows n (fun i=> P i j) x (B*(C*e)):=by
       by_cases hu: Skye.ends j⊆ o.val.2
       · have he:= t _ hr (r j hu); unfold P; simp_rw [if_pos hu]; refine he.paid ?_ |>.mono (max_le le_rfl le_rfl); have hg:=hh j; unfold P at hg; rw [if_pos hu] at hg; rw [hg,norm_zero]; positivity
       apply (allows_const x (by rw [norm_zero]; positivity: ‖(0:SU.group.Color)‖≤ B*(C*e))).germ (Eventually.of_forall fun i=> (if_neg hu).symm)
    refine ((hp j).smul v⁻¹).mono ?_
    rw [abs_of_nonneg (inv_nonneg.mpr (he.le.trans hx))]; apply (inv_mul_le_iff₀ (he.trans_le hx)).mpr; have ht:= mul_le_mul_of_nonneg_right hx (mul_nonneg hp' (by assumption :0≤C)); linarith only [ht] -- hp collision
 have hey:k x=0:=by unfold k Function.comp; rw [show P x=0 from funext hh,map_zero]
 have hy:Agrees o.val.2 (V x) (H' x):=fun j u _=>by unfold H'; rw [show P x=0 from funext hh,Forge.born]
 have hY: ∀ᶠ u in 𝓝 x,Agrees o.val.2 (H' u) (V u):=by
    have ht(j:Bond (More m))(y:Skye.ends j⊆o.val.2):∀ᶠ u in 𝓝 x, H' u j= V u j:=by
       by_cases u:j∈I
       · have hc':ContinuousAt (fun i:E=>(V i j,(1:SU.E))) x:=(hc j y).prodMk continuousAt_const; filter_upwards [hc'.eventually (fleck (V x j, (1:SU.E))).2.2] with u' v; unfold H' gyrate Function.comp increment; rw [steadyB, if_pos u]; unfold P; rw [if_pos y]; exact congrArg Prod.fst v
       filter_upwards [p _ y u] with z v; unfold H' gyrate Function.comp increment; rw [steadyB,if_neg u]; simp [v]
    filter_upwards [eventually_all.mpr (fun j:Bond (More m)=>eventually_all.mpr (ht j))] with x' v' using fun j y z=> v' j (insert_subset y (singleton_subset_iff.mpr z))
 have heK:= Prism.skin hK
 rw [L] at heK
 refine Allows.germ (((show Allows n _ (k x) K from hey.symm ▸ heK).comp (allows_pi (mul_nonneg hp' hp) hP)).mono ?_) ?_ -- tune Allow.pi
 · unfold composeCost; have hL:=hK.grade; apply le_trans _ (mul_le_mul_of_nonneg_right (le_max_left ..) hL); unfold T' F composeCost; exact le_of_eq (by ring)
 filter_upwards [hY] with u g; change U (gyrate I (V x) (Prism.trunk H _ (Prism.silo _ _ (P u))))= U (V u); rw [Prism.trench]; exact q _ _ g
end YM.CF.Rue
