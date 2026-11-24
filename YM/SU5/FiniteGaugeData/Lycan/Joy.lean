import YM.SU5.FiniteGaugeData.Lycan.Ostrich
/-! # Actual continuum estimates of high-resolution many-body tilt and second-limit angular cost -/
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
open Stationary
variable {ι:Type*} (F:ι→Grit)
local notation "Μ"=>ι×SU.Slot
abbrev Prodigy(x:ι→Grit)(X:List ι):= Conv (Techn x) (Otter aroma x) X
private lemma scenic(X:List ι){n:ℕ→Side}{m:ℕ→Male}(g:Tendsto (fun i=>(m i).val.val) atTop atTop)(p:Tendsto (fun i=>(n i).val) atTop atTop)(e:∀ i:ℕ, Even (n i).val) : Tendsto (fun i=> Conv (Techn F) (Otter (cello (n i) (m i)) F) X) atTop (𝓝 (Prodigy F X)):=by
 refine priceConv (Techn F) X _ _ ?_; intro i j; simp only [Otter]; split_ifs; exact ((roof (F i.1) (F j.1)).authorized g p e).2; exact tendsto_const_nhds
section
variable {X:List ι}{Z:Paint}(uR:∀ N:Side, Z N 1=lips F X N 1){S:Finset Cover}{ε:ℝ}
variable (h:Real.exp 1≤Λ.x){I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}(K:Universal Y h u v I E)
variable {P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h K R a)
variable (S':RadioCity.Hypothesis Λ l g Y)(P':Titan Λ){f: W (tent Y h)}(hp:Auth (tent Y h) S f Z)
local notation "Kₜ"=> tent Y h
local notation "M0" i:max s:max=> side Y i s
local notation "Ω" s:max i:max k:max=> ((Y.voyage i).X (Y.uv k)).gram s
include uR
private lemma paysV (e:0<ε): ∃ T:ℕ,∀ (M:Male)(L:Side), Even L.val→ T≤ M.val.val→ T≤ L.val →Standing (tickA L) (spar Λ.K.j M (1:Pane L)) → ‖slopeI Z Λ.K.j L M - Prodigy F X‖ ≤ ε:=by
 by_contra! p; choose m n a b v F' t' using p; have he:Tendsto (fun i=>(m i).val.val) atTop atTop:= tendsto_atTop_mono b tendsto_id; have hx:Tendsto (fun i=>(n i).val) atTop atTop:=tendsto_atTop_mono v tendsto_id; have hu:= scenic F X he hx a
 obtain ⟨w,u₀⟩:= (hu.eventually (closedBall_mem_nhds _ e)).exists; apply  (t' w).not_ge; unfold slopeI; rw [Λ.kJ,uR, inkEarn F (n w) (m w) (by have hh:=F' w; rw [Λ.kJ] at hh; exact hh)]; rw [← dist_eq_norm]; exact Metric.mem_closedBall.mp u₀ -- tune automatic omit Y
include K R A S' P' hp
omit uR K R A S' P' hp in
private lemma troopK(p q v:ℂ) :‖p-v‖ ≤ ‖p-q‖+‖q-v‖:=by simpa [dist_eq_norm] using dist_triangle p q v -- omit
lemma tuition(e:0<ε): ∀ᶠ s in atTop, forall Φ: ℕ→ W Kₜ→ₗ[ℂ]ℂ,Sphere Y h K R A Φ→ ‖Φ s f-Prodigy F X‖ ≤ ε:=by
 obtain ⟨T,t⟩:= paysV (Λ:=Λ) F uR (half_pos e)
 filter_upwards [lanterne Y,lantern Y h hp K R A S' P' (half_pos e)] with s p v₀
 obtain ⟨i,H0,a⟩:= (((side_grows Y s h K.pick.grow_i T).and v₀)).exists; obtain ⟨k,U,b,c⟩:= (a.and ((K.pick.pass Y h s (u i)).and (heightZoom Y s T K.pick.grow_k))).exists; let N:= M0 (u i) s; let M:= (Ω s (u i) (v k)).J.M; have hP:= t M N (electionLive (u:=u) Y s i) (c (u i)) H0 (p (u i) (v k) b.enters M).1.tender; intro Φ H; exact (troopK _ (slopeI Z Λ.K.j N M) _).trans ((add_le_add (U Φ H) hP).trans_eq (by ring)) -- tune
lemma tuitionF {Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ}(H:Sphere Y h K R A Φ): Tendsto (fun s=> Φ s f) atTop (𝓝 (Prodigy F X)):=by
 refine Metric.tendsto_nhds.mpr fun ε e=>?_ ; filter_upwards [tuition Y F uR h K R A S' P' hp (half_pos e)] with s p; rw [dist_eq_norm]; exact (p Φ H).trans_lt (half_lt_self e)
omit uR hp
/-- All order UV estimates on actual chiral gauge wire marks, here at native.Support binds geometries. -/
lemma tuitionReal (X:List ι){Φ:ℕ→ W (tent Y h)→ₗ[ℂ]ℂ}(H:Sphere Y h K R A Φ): Tendsto (fun s=> Φ s (courtI F Kₜ X)) atTop (𝓝 (Prodigy F X)):=tuitionF Y F (fun _=>rfl) h K R A S' P' (tribes F Kₜ X) H
-- moving horizon variant. for proof use nested statement (all late n then all late s) and existence diagonal
end
abbrev haloX(O:ι→ι→Gaia)(i j:ι):= O i j -- smoke
-- $ω$ is normalization target before y. power radii per bilocal $r³$.
section
variable {x:ℕ→ι→Grit}{r:ℕ→ℝ}{O:ι→ι→Gaia}{U D:ι→SpinIdx}{σ:ι→Window.Family}{ε:ℝ}
structure Globe (X:ℕ→ι→Grit) (r:ℕ→ℝ)(σ:ι→Window.Family)(U D:ι→SpinIdx)(O:ι→ι→Gaia):Prop where
 basisE:∀ i:ℕ,0<r i
 comes:Tendsto r atTop atTop
 frameE:∀ (i:ℕ)(j:ι),(X i j).σ=σ j ∧ (X i j).u=U j ∧ (X i j).d=D j
 largeE:∀ a b:ι, O a b≠0 ∧ Tendsto (fun i=>riseX (r i) ((X i b).landing-(X i a).launch)) atTop (𝓝 (O a b))
abbrev lint(σ:ι→Window.Family):ι→Finset SU.Slot:= Window.colors ∘ σ
abbrev earthV (i:ℝ):ℂ:=(i:ℂ)^3
abbrev specter (U D:ι→SpinIdx)(O:ι→ι→Gaia)(i j:Μ):ℂ:= if i.2=j.2 then (Onyx.pencil (O i.1 j.1)) (D j.1) (U i.1) else 0
abbrev absoluteP (σ:ι→ Window.Family)(U D:ι→SpinIdx)(O:ι→ι→Gaia)(X:List ι):ℂ:= Conv (lint σ) (specter U D O) X
variable (ω:Globe x r σ U D O)
include ω
lemma rehear(X:List ι): Tendsto (fun i:ℕ=> (earthV (r i))^(X.length)*Prodigy (x i) X) atTop (𝓝 (absoluteP σ U D O X)):=by
 let C (i:ℕ):Μ→Μ→ℂ:= fun a b=> earthV (r i)*Otter aroma (x i) a b; have h:Tendsto (fun i=> Conv (lint σ) (C i) X) atTop (𝓝 (absoluteP σ U D O X)):=by
   refine priceConv (lint σ) X _ _ (fun i j=>?_); unfold C specter Otter; split_ifs; · exact accolade (O i.1 j.1) (ω.largeE i.1 j.1).1 (X:=fun k=> roof (x k i.1) (x k j.1)) (ω.largeE i.1 j.1).2 (fun v=>(ω.frameE v i.1).2.1) (fun v=>(ω.frameE v j.1).2.2) ω.comes ω.basisE
   simp only [mul_zero]; exact tendsto_const_nhds
 apply h.congr'; apply Eventually.of_forall; intro i; rw [show lint σ=Techn (x i) from funext (fun t=> by change Window.colors _=Window.colors _; rw [(ω.frameE i t).1])]; exact silkCost (Techn (x i)) (earthV (r i)) X (Otter aroma (x i))
variable (h:Real.exp 1≤Λ.x){I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→ Family (tent Y h)→ℂ}(K:Universal Y h u v I E)
variable {P:Call Λ l}{J:Wicket Λ l}(R:Rolled Y h u v J P)(A:∀ a:Axis,Repertory Y h K R a)
variable (S':RadioCity.Hypothesis Λ l g Y)(P':Titan Λ){X:List ι}{f:ℕ→ W (tent Y h)}{S:ℕ→Finset Cover}{Z:ℕ→Paint}(hp:∀ i:ℕ,Auth (tent Y h) (S i) (f i) (Z i))(pZ:∀ (i:ℕ)(N:Side),Z i N 1=lips (x i) X N 1)
local notation "Kₜ"=> tent Y h
omit ω in
private lemma beam_Z(T:Finset Cover):Tendsto (positionZ Y h T) atTop (𝓝 0):= by
 apply Tendsto.const_div_atTop; let L:=Λ.R.L; apply Tendsto.comp (g:=fun x:ℕ=>(x:ℝ)) tendsto_natCast_atTop_atTop; apply StrictMono.tendsto_atTop; apply strictMono_nat_of_lt_succ; intro i; change L.val^i < L.val^(i+1); have p:=pow_pos L.property i; have hQ:L.val≥4:=Λ.V.tallX; rw [pow_succ]; exact (Nat.mul_one (L.val^i)).symm.trans_lt (Nat.mul_lt_mul_of_pos_left (show 1<L.val by omega) p)
omit ω in
private lemma scourt(r ε:ℝ)(x y:ℂ)(n:ℕ)(t:0<r)(h:‖x-y‖ ≤ ε/(r^3)^n): ‖earthV r^n*x-earthV r^n*y‖ ≤ ε:= by rw [←mul_sub,norm_mul,norm_pow,earthV,norm_pow,Complex.norm_real,Real.norm_of_nonneg t.le]; exact (mul_le_mul_of_nonneg_left h (by positivity)).trans_eq (by field_simp)
local notation "Ψ"=> ℕ → W Kₜ →ₗ[ℂ] ℂ
local notation "Ω" i:max=> absoluteP σ U D O i
include K R A S' P' hp pZ
lemma tuitionR(i:ℕ)(e:0<ε): ∀ᶠ s in atTop, positionZ Y h (S i) s ≤ ε ∧ forall Φ:Ψ,Sphere Y h K R A Φ→ ‖earthV (r i)^X.length * Φ s (f i)-earthV (r i)^X.length *Prodigy (x i) X‖ ≤ ε:= by
 have t:=ω.basisE i; refine (((beam_Z Y h (S i)).eventually (ge_mem_nhds e)).and ((tuition Y (x i) (pZ i) h K R A S' P' (hp i) (show 0<ε/((r i)^3)^X.length by positivity)).mono fun s y Φ H=> scourt _ _ _ _ _ t (y Φ H))) -- tune
/-- genuine Gram costs at all late observing levels for this particular (fixed-order) Chisel tuple. Allows actual reflections in the mark by pZ stencil. -/
lemma egg(e:0<ε): ∀ᶠ i in atTop, ∀ᶠ s in atTop, positionZ Y h (S i) s ≤ ε ∧ forall Φ:Ψ,Sphere Y h K R A Φ→ ‖earthV (r i)^X.length*Φ s (f i) - Ω X‖ ≤ ε:=by
 filter_upwards [(rehear ω X).eventually (closedBall_mem_nhds _ (half_pos e))] with i p; filter_upwards [tuitionR Y ω h K R A S' P' hp pZ i (half_pos e)] with s hx
 have hh:‖earthV (r i)^X.length*Prodigy (x i) X - Ω X‖ ≤ε/2:=by rw [← dist_eq_norm]; exact mem_closedBall.mp p
 exact ⟨hx.1.trans (half_lt_self e).le,fun Φ H=>(troopK _ _ _).trans ((add_le_add (hx.2 Φ H) hh).trans_eq (by ring))⟩
lemma woolly: ∃ z:ℕ→ℕ,Tendsto z atTop atTop ∧ ∀ y: ℕ→ℕ,z≤ y →
 Tendsto (fun i:ℕ=>positionZ Y h (S i) (y i)) atTop (𝓝 0) ∧
 ∀ Φ:ℕ→ℕ→ W (tent Y h) →ₗ[ℂ]ℂ, (∀ i:ℕ,Sphere Y h K R A (Φ i)) → Tendsto (fun i:ℕ=> earthV (r i)^X.length * Φ i (y i) (f i)) atTop (𝓝 (absoluteP σ U D O X)):=by
 choose z Hz using fun i:ℕ=> eventually_atTop.mp (tuitionR Y ω h K R A S' P' hp pZ i (one_div_pos.mpr (ω.basisE i))); let j i:= max i (z i); refine ⟨j,tendsto_atTop_mono (fun i=>le_max_left i _) tendsto_id,fun y t=>?_⟩; let H0(i:ℕ):= Hz i (y i) ((le_max_right ..).trans (t i)); have h:=Tendsto.const_div_atTop ω.comes 1
 refine ⟨squeeze_zero (fun i=>by unfold positionZ; positivity) (fun i=>(H0 i).1) h,fun Φ H=> ?_⟩; apply (rehear ω X).congr_dist; refine squeeze_zero (fun _=>dist_nonneg) (fun i=>?_) h; rw [dist_comm, dist_eq_norm]; exact (H0 i).2 _ (H i)
omit hp pZ
lemma wool_f(X:List ι): ∃ z:ℕ→ℕ,Tendsto z atTop atTop ∧ ∀ y:ℕ→ℕ,z≤ y → Tendsto (fun i=>positionZ Y h (band (x i) X) (y i)) atTop (𝓝 0) ∧ ∀ Φ:ℕ→ℕ→ W (tent Y h) →ₗ[ℂ]ℂ, (∀ i:ℕ,Sphere Y h K R A (Φ i))→ Tendsto (fun i:ℕ=>earthV (r i)^X.length * Φ i (y i) (courtI (x i) (tent Y h) X)) atTop (𝓝 (absoluteP σ U D O X)):=woolly Y ω h K R A S' P' (fun i=>tribes (x i) Kₜ X) fun i N=> rfl
end
#print axioms wool_f
#print axioms woolly
end Sesame
end Chiffon
end YM.CF.Buffered.Afterglow.Hierarchy.LyraBill
