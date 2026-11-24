import YM.CF.Buffered.Reverie
/-!
# Ship the MEAN of each local advancing mark across periods.

Need local-marginal-matches for `LoomLaw2`, in the interior. This is an **additional choice**
condition in using lemma loomloc: its repetition-alone bullet is pointwise, not in law.
Here uses the choice described gaugeM which arranges equality of law
on these cones, not offered by previously checked constructors. Explicit assumption
on the chosen paired Looms at level k (doesn't assert any match of pressure ratios etc.).
-/
set_option autoImplicit false
set_option maxHeartbeats 610000
set_option synthInstance.maxSize 26000
noncomputable section
namespace YM.CF.Buffered.Mail.Grok
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Phase MeasureTheory RG Wilson Branch
open Region Roost Rails Mil Fock Scroll Spire Push.SectorMeasure Ordered Cin Tree Tulip Rush Lifted Heat Solid Burn Advance Vale Skye Stencil
open Further.PhysicalPeriodLimitF933 Macrame Crust Grid Push.GridApprox Tenant Laurent Bloch Next.Free Fir Peaks Scree Drapes Tap Dial Reflect Window
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {K V C F k p N P L D M B B' l c f:Side}{G:Gauge}{S:Patch}
variable (A:Planck N P D)(Y:Loom N)(y:Loom P)(h:Measurable y)(kY:Measurable Y)(I: Support (More N))
local notation "Θ" => weave (G:=SU.group) (gauge_plan A)
def LoomLaw2 (A:Planck N P D)(Y:Loom N)(y:Loom P)(I:Support (More N)): Prop:= ∀ v:Pane P,(depot N).map (fun x=> extract I (Y (weave (gauge_plan A) v,x)))=(depot P).map (fun x=> extract I (weave (gauge_plan A) (y (v,x))))
private def restored (I: Support (More N))(v:LEData I): Pane N := fun x=> if g:x.1∈ I∧x.1+step x.2∈I then v ⟨x,g⟩ else 1
private lemma restored_m : Measurable (restored I) :=by apply measurable_pi_lambda; intro x; unfold restored; split; exact measurable_pi_apply _; exact measurable_const
-- keep assumption as equality of law on same I projecting the two fields, no linear precondition.
include kY h in
private lemma refund (W:LoomLaw2 A Y y I) {Z:Type*}[MeasurableSpace Z][NormedAddCommGroup Z][NormedSpace ℝ Z][BorelSpace Z][SecondCountableTopology Z]
 (f:Pane N→ Z)(m:Measurable f)(p:LocalOn I f)(v:Pane P): (∫ i,f (Y (Θ v,i)) ∂depot N) =∫ i,f (Θ (y (v,i)))∂depot P :=by
 let R(z:LEData I):=f (restored I z); have hx(z:Pane N): R (extract I z)=f z:=by
    apply p; intro i t u; rw [restored, dif_pos (show i.1∈ I∧i.1+step i.2∈I from ⟨t,u⟩)]; rfl
 have he{A:Type}[MeasurableSpace A] (x:A→ Pane N)(p:Measurable x)(μ:Measure A): (∫ i,f (x i)∂μ)=∫ i,R i∂μ.map fun v=> extract I (x v):=by rw [integral_map (φ:=fun v=> extract I (x v)) (f:=R) ((extract_mp _).comp p).aemeasurable (m.comp (restored_m I)).aestronglyMeasurable]; simp_rw [hx]
 rw [he (fun i:Ids N=>Y (Θ v,i)) (kY.comp (measurable_const.prodMk measurable_id)), he (fun i:Ids P=>Θ (y (v,i))) ((weave_cont ..).measurable.comp (h.comp (measurable_const.prodMk measurable_id))),W v]
private def intoC {I J:Type*}[LinearOrder I][LinearOrder J][Fintype I][Fintype J](f:I↪J) : FC I→L[ℝ] FC J:= LinearMap.toContinuousLinearMap ((into f).toLinearMap.restrictScalars ℝ)
private lemma remit {I J:Type*}[LinearOrder I][LinearOrder J][Fintype I][Fintype J](f:I↪ J){E:Type*}[MeasurableSpace E](μ:Measure E){Z:E→ FC I}(p:Integrable Z μ): (∫ i,into f (Z i)∂μ)=into f (∫ i,Z i∂μ):= (intoC f).integral_comp_comm p
variable (A':Planck F f D)
variable (J:Planck (More N) B' k)(E:Planck (More P) B' l)
variable {ℓ:F.val=N.val*S.L.val}{d:f.val=P.val*S.L.val}{w e z:ℕ}(i:2 ≤ (More P).val)
variable (j:ℕ)(q:Chi)(r:ℝ)(Q:Op SU.Slot)(M':Male)(H: LaurentRadius j S.L z)
-- package geometry
structure Clear (A:Planck N P D)(A':Planck F f D)(J:Planck (More N) B' k)(w e z:ℕ)(ℓ:F.val=N.val*S.L.val): Prop where
 fit : 2*z+1≤ w
 toast : padded (decreed ℓ) (wallZ J 0 w) (clothRadius S.L z) ⊆ blockF (gauge_plan A') 0
 inner : halo e (halo (nearZero z) (wallZ J 0 w)) ⊆ blockF (gauge_plan A) 0
variable {b:Bool} (c':Clear A A' J w e z ℓ){a:Mark N}{g:Mark P}(t:AtSupport b (wallZ J 0 w) a)(p':AtSupport b (wallZ E 0 w) g)(v: CoherentV A g a) (U:Fields f)(V:Fields P)
local notation "s"=> decreed ℓ
local notation "W₀"=> decreed d
local notation "Lq"=> Lace.project (P:=S) (h:=ga (K:=S.L) d) (H:=ga (K:=S.L) ℓ) (Planck.ratio (gauge_plan A)) i
local notation "m"=> modeO A' 0
local notation "V'"=> wallZ J 0 w
local notation "R₀"=> S.odd_side
local notation "G₀"=> halo (nearZero z) (wallZ J 0 w)
include c' v p' H
lemma fitted (T:Forest (ratio (decreed d))) : before s j Q M' R₀ q r a ((Lq).repeater T) (recurM A' U) (recurM A V)= into m (before W₀ j Q M' R₀ q r g T U V):=by
 unfold before; rw [v]; let y:=middle W₀ q r T U V; have hx: middle s q r ((Lq).repeater T) (recurM A' U) (recurM A V)=(weave (G:=SU.group) (gauge_plan A') y.1,weave (G:=SU.group) (gauge_plan A) y.2):= Prod.ext (stream A A' i q r T _ _) rfl
 rw [hx]; exact stitched A A' J E j Q M' H c'.fit c'.toast y.1 y.2 (p'.allV V)
include t i
lemma stand : gathered s j Q M' R₀ q r a (recurM A' U) (recurM A V)=into m (gathered W₀ j Q M' R₀ q r g U V):=by
 unfold gathered; let G':=fun T:Forest (ratio s)=> before s j Q M' R₀ q r a T (recurM A' U) (recurM A V); let k(T:Forest (ratio W₀)):= before W₀ j Q M' R₀ q r g T U V
 have hx: ∀ X Y, sameForest (blockF (gauge_plan A) 0) X Y → G' X=G' Y:= fun X Y h=> before_local s j Q M' R₀ V' H q r t (fun _ _ _ =>rfl) (fun _ _ _=>rfl) (fun _ _ _=>rfl) (fun i p=> h i (c'.inner (halo_subset e _ p)))
 have he:= reduces (ℓ:=ga (K:=S.L) ℓ) (d:=ga (K:=S.L) d) (gauge_plan A) i G' (fun T=> into m (k T)) (fun X Y h=> hx X Y h) (fun j'=> fitted A A' J E i j q r Q M' H c' p' v U V j') -- order
 apply Eq.trans he; unfold avgF; rw [into_real, map_sum]; rfl
local notation "Xv"=> recurM A' U
local notation "x'"=> assembled W₀ j Q M' R₀ q r y g U
local notation "y'"=> assembled s j Q M' R₀ q r Y a Xv
open Next.SectorChange
variable (Z:LoomLaw2 A Y y (halo (nearZero z) (wallZ J 0 w)))(u':0<r)(r':2*r<firstRadius SU.group)
include Z u' r' h kY
lemma assembledV (x:Pane P) : y' (Θ x)= into m (x' x):=by
 let g'(v:Pane N):=gathered s j Q M' R₀ q r a Xv (Θ x,v); have hx:= (env_gathered s j Q M' R₀ q r H u' r' a t.env).meas; have hm: Measurable g':=hx.comp (f:=fun w: Pane N =>(Xv, (Θ x,w))) (measurable_const.prodMk (measurable_const.prodMk measurable_id))
 have hp: LocalOn G₀ g':=fun _ _ H'=> gather_dep s j Q M' R₀ q r H a t Xv Xv (fun _ _ _=>rfl) _ _ (fun _ _ _=>rfl) H'
 let f'(x: Fields P):= gathered W₀ j Q M' R₀ q r g U x; let i'(w:Ids P):=(x,y (x,w)); have he(X:Pane P): g' (Θ X)= into m (f' (x,X)):= stand A A' J E i j q r Q M' H c' t p' v U (x,X)
 have ht: Integrable (fun w:Ids P=> f' (i' w)) (depot P) := Env.integrableX (Env.along (g:=fun w=> (U, i' w)) (env_gathered W₀ j Q M' R₀ q r H u' r' g p'.env) (measurable_const.prodMk (measurable_const.prodMk (h.comp (measurable_const.prodMk measurable_id))))) _
 change (∫ i,g' (Y (Θ x,i)) ∂depot N)= into m (∫ w:Ids P, f' (i' w)∂depot P); rw [refund A Y y h kY G₀ Z g' hm hp x]; simp_rw [he]; exact remit _ _ ht
variable (K:KernelChoices)(dK:S.Branches K SU.group) (β:ℝ) (Y': LoomLaw Y e)
local notation "L'"=> stepped K (P:=S) (ga (K:=S.L) ℓ)
local notation "K'"=> stepped K (P:=S) (ga (K:=S.L) d)
include dK Y'
lemma rates : CoherentV A' (pushMark W₀ K' j Q M' R₀ q r β y g) (pushMark s L' j Q M' R₀ q r β Y a) :=by
 intro U; let f'(x:Pane P):=assembled W₀ j Q M' R₀ q r y g U x; let k(x:Pane N):=assembled s j Q M' R₀ q r Y a (recurM A' U) x; let V:=halo e G₀
 have hY : k ∘ Θ = fun x=>into m (f' x):= funext fun x=> assembledV A Y y h kY A' J E i j q r Q M' H c' t p' v U Z u' r' x
 let a'(x:Pane P):= (K').density β U.1 x; have ht':Envelope f':= env_fixed W₀ j Q M' R₀ q r y H h u' r' g p'.env _; have hv:Envelope k:= env_fixed s j Q M' R₀ q r Y H kY u' r' a t.env _; let y := prior SU.group (More P)
 have hm:Envelope (fun x=>into m (f' x)):= Girt.pole_w _ (into m) (into_cont _) ht'
 change linkLaw L' β k (recurM _ U).1=into m (linkLaw K' β f' U.1)
 change linkLaw L' β k (recurM A' U).1=into m (∫ x:Pane P,a' x • f' x∂prior SU.group (More P)); rw [← remit m y (Env.integrableX (Env.scale (show Envelope a' from slice_env K' β dK U.1) ht') y)]; simp_rw [into_real]; change _=linkLaw K' β (fun x=>into m (f' x)) U.1
 have hl:LocalOn V k:=fun x z a'=> asm_dep s j Q M' R₀ q r Y H kY u' r' a t Y' (recurM A' U) (recurM A' U) (fun _ _ _=>rfl) x z a'
 ext i l
 rw [coordinate_law L' β dK hv,coordinate_law K' β dK hm]
 let w(x:Pane N):= k x i l; have he:∀ (x:Pane P), w (Θ x)= into m (f' x) i l:=fun x=>congrFun (congrFun (congrFun hY x) i) l
 rw [show (fun x:Pane P=> into m (f' x) i l)= w ∘ Θ from funext fun x=> (he x).symm]; exact Radiant.joint_step (gauge_plan A) ‹2 ≤ (More P).val› K β U.1 V c'.inner w (fun _ _ t=> congrFun (congrFun (hl _ _ t) _) _) (coordinate_env _ _ hv) dK
end YM.CF.Buffered.Mail.Grok
#print axioms YM.CF.Buffered.Mail.Grok.rates
