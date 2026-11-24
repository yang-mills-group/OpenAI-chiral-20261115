import YM.SU5.FiniteGaugeData.Stent.Puff
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
set_option linter.unusedVariables false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Window.Brique
open Reed (Fine)
attribute [local instance] opCStarAlgebra
set_option quotPrecheck false
open Heat Quest Fock.Brique
open Nacre Heat Charm Chrono Journey
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
open SalonG
open Quest.Chaperone
open Steam
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l)) {g:ℝ}{u v:ℕ→ℕ}
open Eight YM.SU5.FiniteGaugeData.CodaT YM.SU5.FiniteGaugeData.Cuprite.Spirit YM.SU5.FiniteGaugeData.Cuprite.Spirit.Vapors Fock.Relief Rhythm.Hush Rhythm.CodaT Dial Aria Reduction.Drama.Pack
open Rhythm.Dolores Rhythm.Ergo Hills Gamer Fock.Reduction Turnist Alts Alts.Emblem Window.Presidio.Nigra
namespace Chiffon
open Moorend Rhythm.CodaT
open Reduction.Loyd Reduction.Dijon Reduction.Loyd.Art Reduction.Celeste
namespace Sesame
open Reduction Lycan Niagara Chisel Largo Mirage Cascade Ember PolarF Onyx
open Reduction.Plush Window.Trigo
namespace FlakeNight
open Fock Tint -- gauge
local notation "X"=> Trigo.Chamber true -- Window opened
local notation "Y₀"=> Trigo.Chamber false
local notation "Υ" n:max=> SU.Slot × Fin n
variable {n m:ℕ}
local notation "Δ"=> Fin (projCard n)
open CF.Stent Buffered.Stent
open Tint Next.Rank
variable (k:Spindle.Rules SU.group)(t:ℝ)(h':Real.exp 1≤Λ.x)
local notation "Kₜ"=> (tent Y h')
local notation "D₁"=> aliasLaw Λ
local notation "F₁"=> reamW Λ.R (aliasLaw Λ)
local notation "d"=> Λ.J.d
variable (f:Fin (n+1)→ X)(g':Fin (n+1)→ Y₀)(s i r:ℕ)
local notation "N₀"=> side Y i s
local notation "N₁"=> side Y i (s+1)
local notation "τB"=> bedfield Λ.R.L Λ.J.n
local notation "τA"=> bedH (bedfield Λ.R.L Λ.J.n) t
local notation "π"=> Base f g' (tent Y h')
noncomputable abbrev Auxiliary (Λ:Preparation)(t:ℝ)(K:Calibration):= shunt K true (bedH (bedfield Λ.R.L Λ.J.n) t) (healCare ..)
noncomputable abbrev Neon (Λ:Preparation)(b:Bool)(K:Calibration):= shunt K b (Nylon Λ.R) (locketA Λ.R Λ.V.tallX)
local notation "ξ"=> Auxiliary Λ t Kₜ
local notation "ν"=> Neon Λ true Kₜ
local notation "τ"=> Vst f g' (tent Y h')
local notation "L₁"=> PaceLock Λ.R (rayCost Y s i r)
local notation "ΦX"=> GridStep Λ l rayW
local notation "ω"=> Warp 0 Kₜ
lemma warploc : Locator Kₜ (Warp 0 Kₜ) rayW:=by
 let m:= starlit 0; let w:= reedW 0; exact (tote (roseone m) (roseone w) _ (by unfold footprint rayW; simp [roseone,m,starlit]) (by unfold footprint rayW; simp [roseone,w,reedW])).widen -- fill
noncomputable abbrev Iq :Catalog rayW:= reading Kₜ _ (Warp 0 Kₜ) (warploc Y h') -- trouble notation included? h' missing? identify
local notation "Ζ" i:max r:max=> composeQ (tent Y h') (GridStep Λ l rayW) ((snag Y h' rayW s i r) (Iq Y h'))
variable (q:Rack true (reamW Λ.R (aliasLaw Λ)) f)(a:Rack false (reamW Λ.R (aliasLaw Λ)) g') (h₂: f 0=starlit (specialM Λ.R.L))(h₃: g' 0=reedW (specialM Λ.R.L))
variable (p:0<t)(e:earlyAux k Λ t)
include q a h₂ h₃ p e
private lemma sinfonia (V:Offered Y rayW s i r)(h: 2*(Λ.R.L.val/2+1)<(More N₁).val)(t':2* D₁ < (N₀).val)(uₕ: Hosp (reamW Λ.R (aliasLaw Λ)) N₁):
 sold Y h' (s+1) i ((ξ).val*((τ).val*(Ζ i r)))=sold Y h' (s+1) i ( L₁ • ((ξ).val*((Neon Λ true Kₜ).val*(π).val))) :=by
 let Z:= Ζ i r
 have hz:sold Y h' (s+1) i Z= ingress Y s i r (sold Y h' s i (Warp 0 Kₜ).val):=by unfold Z; rw [snag_pay Y h' rayW s i r V, show sold Y h' (s+1) i (composeQ _ _ _) = ingress Y s i r _ from (sold_ticket Y h' rayW s ⟨(i,r),V⟩ (Iq Y h'))]; unfold Iq; rw [reading_p]
 funext W; rw [map_smul,sold_mult,sold_mult Y h' (s+1) i (τ).val Z,sold_mult,sold_mult]; simp only [Pi.smul_apply,Pi.mul_apply]; rw [hz]; by_cases b:bedH (bedfield Λ.R.L Λ.J.n) t (onC (side Y i (s+1)) W.2)=0
 · unfold Auxiliary; rw [sold_shunt]; dsimp only; rw [if_pos rfl, b,zero_smul,zero_mul,zero_mul,smul_zero]
 rw [Wool Y k t h' f g' s i r V q a h₂ h₃ p e h t' uₕ W b]; unfold Neon; rw [show sold Y h' (s+1) i (shunt Kₜ true (Nylon Λ.R) _).val W=Nylon Λ.R (onC N₁ W.2) • 1 from (congrFun (sold_shunt Y (Nylon Λ.R) (locketA Λ.R Λ.V.tallX) true h' (s+1) i) W)]; rw [Algebra.smul_mul_assoc, one_mul,←smul_smul,Algebra.mul_smul_comm]
#print axioms sinfonia
section
variable {P:Call Λ l}{J:Wicket Λ l}{I:ℕ→Family (tent Y h')→ℕ→ℂ}{E:ℕ→Family (tent Y h')→ℂ}
variable (K:Universal Y h' u v I E)(R:Rolled Y h' u v J P)
include K
omit q a h₂ h₃ p e in
private lemma dualAge (r:ℕ→ℕ)(p: eligiblePath Y u v r): ∃ (Q:Op SU.Slot)(x:ℕ→ℕ), StrictMono x ∧ Tendsto (fun j:ℕ=> rayCost Y s (u (x j)) (v (r (x j)))) atTop (𝓝 Q):=by
 let C:= Λ.R0 (hat Λ.R.L Λ.x s); let W(i):= rayCost Y s (u i) (v (r i)); obtain ⟨x,hx,p'⟩:= extraction_of_frequently_atTop ((eligible_offer Y h' rayW s K r p).frequently); have L(i:ℕ):W (x i)∈ closedBall (0:Op SU.Slot) C:= mem_closedBall_zero_iff.mpr (((Y.voyage (u (x i))).X (Y.uv _)).pull.tip s (p' i).age); obtain ⟨q,_,a,w,t⟩:= (isCompact_closedBall (0:Op SU.Slot) C).tendsto_subseq L; exact ⟨q,x∘a,hx.comp w,t⟩ -- K not include.Ou
include K R
lemma Franc : ∃ y:ℂ,y≠0∧ Auxiliary Λ t Kₜ * (Vst f g' Kₜ * Charm.next Y h' s K R (Warp 0 Kₜ))= y • (Auxiliary Λ t Kₜ*(Neon Λ true Kₜ*Base f g' Kₜ)):=by
 obtain ⟨x,hx⟩:= eligible_exists Y u v K.pick.grow_k; obtain ⟨Q,o,a',X'⟩:= dualAge Y h' s K x hx; let Θ:= PaceLock Λ.R Q; let κ(i:ℕ):= PaceLock Λ.R (rayCost Y s (u (o i)) (v (x (o i))))
 let A:= Auxiliary Λ t (tent Y h'); let B:= Neon Λ true Kₜ; let M:= Charm.next Y h' s K R (Warp 0 Kₜ); let S(i:ℕ):=snag Y h' rayW s (u (o i)) (v (x (o i))) (Iq Y h'); let T:=P rayW s (Iq Y h'); let G':= composeQ Kₜ (GridStep Λ l rayW); have hg: M.val= G' T:= keeps Y h' rayW s K R _ (warploc Y h'); have he:Tendsto κ atTop (𝓝 Θ):= (Pace.cont Λ.R).continuousAt.tendsto.comp X'; have ht:Tendsto S atTop (𝓝 T):= (audition _ _ (calls Y h' rayW s R x hx) (tendsto_const_nhds (x:=Iq Y h'))).comp a'.tendsto_atTop
 obtain ⟨S₁,v₁⟩:= testimony Kₜ (A*(B*π)); obtain ⟨S₂,v₂⟩:= testimony Kₜ A; obtain ⟨S₃,v₃⟩:= testimony Kₜ τ; let H:= S₁∪(S₂∪(S₃∪GridStep Λ l rayW)); have hp:S₂⊆H:=Subset.trans subset_union_left subset_union_right; have hw:S₃∪GridStep Λ l rayW ⊆ H:=Subset.trans subset_union_right subset_union_right
 let D(x:ℕ):= A.val *((τ).val* G' (S x)); let Y'(i:ℕ):=κ i • (A*(B*π)).val; have hF: D =ᶠ[atTop] Y':=by
    let v'(i:ℕ): InTest _ true H false (D i):= ((show InTest Kₜ true _ _ A.val from v₂).mono hp).mul (((show InTest _ true _ _ (τ).val from v₃).mono (Subset.trans subset_union_left hw)).mul ((compose_t (GridStep Λ l rayW) Kₜ (S i)).mono (Subset.trans subset_union_right hw))); -- v shadows period!! rm
    have hh':= eligible_offer Y h' rayW s K x hx; -- shadow remove
    filter_upwards [a'.tendsto_atTop.eventually hh', a'.tendsto_atTop.eventually (enoughR Y h' K H (s+1)), a'.tendsto_atTop.eventually (side_grows Y (s+1) h' K.pick.grow_i (2*(Λ.R.L.val/2+1)+1)), a'.tendsto_atTop.eventually (side_grows Y s h' K.pick.grow_i (2*D₁ +1)), a'.tendsto_atTop.eventually (enoughR Y h' K (reamW Λ.R (aliasLaw Λ)) (s+1))] with i e₁ e₂ e₃ e₄ e₅; let N:= side Y (u (o i)) (s+1); change D i=Y' i; obtain ⟨a₁,h⟩:= Hierarchy.certify H Kₜ (D i) (v' i); obtain ⟨b,v₁'⟩:= Hierarchy.certify H Kₜ (Y' i) ((show InTest _ _ _ _ _ from v₁).mono subset_union_left|>.smul (κ i)); rw [←h,←v₁']; apply congrArg; apply sold_catalog_inj Y h' H (s+1) _ (roomy_hosp H e₂); let p':= sinfonia Y k t h' f g' s _ _ q a h₂ h₃ p e e₁ (by change _ ≤ N.val at e₃; change _ < N.val*2; omega) e₄ (roomy_hosp _ e₅); dsimp only; rw [h,v₁']; exact p' -- tune `.comp_apply` likely no. vars shadows.
 refine ⟨Θ,Pace.money Λ.R Λ.V.tallX Q,?_⟩; apply Subtype.ext; funext i z; change A.val i z*((τ).val i z*M.val i z)= Θ • (A*(B*π)).val i z; rw [hg]; exact tendsto_nhds_unique_of_eventuallyEq (tendsto_const_nhds.mul (tendsto_const_nhds.mul ((eval_c Kₜ (GridStep Λ l rayW) i z).continuousAt.tendsto.comp ht))) (he.smul_const _) (hF.mono (fun j p=> congrFun (congrFun p i) z))
#print axioms Franc
end
end FlakeNight
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
