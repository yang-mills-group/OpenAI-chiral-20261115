import YM.SU5.FiniteGaugeData.Signal.Polling
/-! # Actual gain through DCT and local prices. No positive state approximation assumed. -/
set_option autoImplicit false
set_option linter.flexible false
set_option maxHeartbeats 760000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Signal
open Function Filter NormedSpace MeasureTheory Finset Lattice RG Wilson Fock Lat Cube SU Scroll Spire Tulip
open Window Mir Skye Scree Rush Dial Laic Thera Nacre Drapes Paige Vault Peaks Cascade Hive
open Buffered Buffered.Afterglow Buffered.Advance Reef Hom Tenant Branch Buffered.Concord Buffered.Afterglow.Satin Lifted
open MeasureTheory Push.SectorMeasure Girt
open scoped Topology ContDiff InnerProductSpace BigOperators Matrix MatrixOrder ComplexOrder Kronecker Classical Matrix.Norms.L2Operator ComplexConjugate Pointwise
attribute [local instance] opCStarAlgebra
open Supplies Sparkle Sparkle.Condense Sparkle.Portage Sparkle.Circuit Pastel Momentum Furnace
open Scherzo Kinetic Play Py Py.Rate LocalLimit Preparation Skyscraper IgnoreFog Vale Period
open Buffered.Reliance Buffered.Reliance.ShortWave Afterglow Afterglow.Journey
open Boon Graph Pressure Esti Jade.Earn Phase CF.Laic CF.Ember
namespace Showcasing
open Metric Ovation
variable {M N n m:Side}(ℓ:Loom M){D:Orbit M→ Phys M}
variable (K: Calibration){x: junior K} (p:Face ℤ) {S T:Finset Cover}{A ε u ξ C:ℝ}

local notation "Z·" a=> ablate {p} a K

def visible (K:Calibration)(p:Face ℤ){S:Finset Cover}(v:restsOn {p} S)(a:ℝ)(x:junior K):= (ablate {p} a K v)*x
lemma visible_view (t:restsOn {p} T)(V:Fields (K.c n))(a:ℝ)(x:junior K) : (visible K p t a x).val n V = if a ≤ SU.group.chord (faceValue (onC _ V.1) p) then x.val n V else 0 := by
 change (ablate {p} a K t).val n V * x.val n V = _; rw [cast_toll]; by_cases h:a ≤ SU.group.chord (faceValue (onC _ V.1) p)<;> simp [crowded,h]
lemma shining (h:C>0)(t:restsOn {p} T)(w:∀ v, ‖x.val n v‖≤ C) (a:ℝ) (i:Fields (K.c n)): ‖(visible K p t a x).val n i‖ ≤ C:=by rw [visible_view K p]; split; exact w _; rw [norm_zero]; exact h.le
-- all roomy; transport enough, sat same assignment. Finance exact. 
lemma taking (v:K.c m=M)(t:restsOn {p} S)(x:junior K)(e:Measurable ℓ)(Q:Integrable D (city M)) :
    Tendsto (fun n:ℕ=> markedRead (v ▸ (visible K p t (Meter n) x).val m) ℓ D) atTop (𝓝 (markedRead (v ▸ x.val m) ℓ D)):=by
 subst M; let W:= (K.c m); let q:Face (Per (More W)):= (wrap (More W) p.1,p.2); let V:=fun i:Orbit W=> letterRead (x.val m (drawn ℓ i)) (D i); let F(n:ℕ)(i:Orbit W):=letterRead ((visible K p t (Meter n) x).val m (drawn ℓ i)) (D i)
 have ht(n:ℕ)(i:Orbit W): F n i=if Meter n ≤ SU.group.chord (faceValue i.1 q) then V i else 0:=by
    unfold F; rw [visible_view, tile_face]; change letterRead (if Meter n ≤ SU.group.chord (faceValue i.1 q) then _ else _) _=_; split; rfl; next h=>
     change letterRead 0 _=0; change (Plum.listen (D i)) 0=_; rw [map_zero]
 have he(x:junior K): Integrable (fun i:Orbit W=> letterRead ((x.val m) (drawn ℓ i)) (D i)) (city W):= by
    apply mark_integrable e _ Q; let u:=supported K x; exact (show InTest K true u.choose false x.val from u.choose_spec).support m|>.env -- tune
 change Tendsto (fun n=>∫ i, F n i ∂city W) atTop (𝓝 (∫ i,V i ∂city W)); refine tendsto_integral_of_dominated_convergence (fun i=>‖V i‖) (fun n=> (he (visible K p t (Meter n) x)).aestronglyMeasurable) (he x).norm (fun n=>Eventually.of_forall (fun i:Orbit W=>?_)) ?_
 · rw [ht]; split; rfl; simp
 filter_upwards [displacement W q] with i v; apply tendsto_const_nhds.congr'; filter_upwards [meter_time.eventually (ge_mem_nhds v)] with n w; exact ((ht n i).trans (if_pos w)).symm
-- preservation of basal read vs cutoff, row & supporting E
variable {P:Preparation}{l:ℕ}(Y: Course P (VolumeCape.Dream.Nimbus l))(H : Real.exp 1 ≤ P.x)(s:ℕ)
variable (v:restsOn {p} T) {i k:ℕ→ℕ}
variable {I:ℕ→Buffered.Family (tent Y H)→ℕ→ℂ}{E:ℕ→Buffered.Family (tent Y H)→ℂ}{X:Playhouse P l}
local notation "Λ"=> tent Y H
variable (W:Traced Y H i k I E X)(x:junior (tent Y H))(r:x∈ club (tent Y H) T)
lemma raised (n d:ℕ)(w:Ferry Y s n d) : Tendsto (fun r=> sharp Y H s n d (visible (tent Y H) p v (Meter r) x).val) atTop (𝓝 (sharp Y H s n d x.val)):=by
 let k:=(Y.voyage n).X (Y.uv d); let L:= (Y.voyage n).CapeT s
 exact (taking L (tent Y H) p (m:= momentm Y n s) (terrain Y H (Y.ir n) s) v x ((Y.voyage n).ownership s).paid.bill (Marks.can_read _ _ _ L w.fire.priceA)).div_const _
include W r
-- E for these chosen stencils. no need claim uniform in stencil.
theorem maintained(h:0 < C)(g:∀ (m:Side) v, ‖x.val m v‖≤ C): Tendsto (fun n=> E s (visible (tent Y H) p v (Meter n) x).val) atTop (𝓝 (E s x.val)):=by
 let Y'(n):=visible (tent Y H) p v n x; let f:=Y'; let C₁:=C; let z:= E s x.val
 refine Metric.tendsto_nhds.mpr fun ε e=>?_; have he: ε/4 >0:= by positivity
 have hz:Tendsto (fun i=>Meter i*C) atTop (𝓝 0):= by simpa only [zero_mul] using meter_time.mul_const C
 obtain ⟨n,l,hc⟩:= ((W.crimson T s).and (hz.eventually (gt_mem_nhds he))).exists -- tune ge etc
 obtain ⟨d,qd,t⟩:= ((cadence Y k W.own.pick.grow_k (i n)).and (W.own.pick.pass Y H s (i n))).exists
 let q(y:junior Λ):= sharp Y H s (i n) (k d) y.val; have hw(y:junior (tent Y H))(p:y ∈club (tent Y H) T)(t:∀ (m:Side) v, ‖y.val m v‖ ≤ C): ‖q y-E s y.val‖≤ ε/4:= ((l.2 _ p C (t _)).2 d qd).trans (show _ < _ from hc).le
 have ht:=hw _ r g; filter_upwards [(Metric.tendsto_nhds.mp (raised p Y H s v x (i n) (k d) t) (ε/4) he)] with m pm
 rw [dist_eq_norm] at pm ⊢; let u:=f (Meter m); change ‖q u-q x‖<_ at pm; let F:= E s u.val
 have hu: ‖F-q u‖ ≤ ε/4:=(norm_sub_rev ..).trans_le (hw u ((club (tent Y H) T).mul_mem (clamp_pay {p} _ v) r) (fun m=> shining Λ p h v (g m) (Meter _))) -- m binder shadow fix
 refine (norm_sub_le_norm_sub_add_norm_sub F (q u) (E s x.val)).trans_lt ?_; linarith only [pm,hu,ht,norm_sub_le_norm_sub_add_norm_sub (q u) (q x) (E s x.val),e]
end Showcasing
end YM.CF.Signal
#print axioms YM.CF.Signal.Showcasing.maintained
