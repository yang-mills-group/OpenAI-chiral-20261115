/- This file incorporates modified third-party source. See the source attributions in notices/. -/ import YM.SU5.Registration.Momenta.Portraits
/-!
 # Null labels, equivalence via actual joint stencil table. Permuting labels.
 Preserve all inertia properties for operator system on this station. No comparison with
 different-spectrum namespaces. Adapted `YM/Work/C26`, `YM/SU5/FiniteGaugeData/Cirrus/Scepter, Saffron`.
 Use equivalence for rank investigations further.
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.Carton
open Function Set Filter MeasureTheory Measure Complex Submodule SatinRegistration
open Boundary Probe Mink Mink.Poincare Multiplier Roy Spectral OS.Semigroup SatinEdge.RealSheet
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexOrder
variable {H:Hilbert}{S: _root_.YM.OS.Semigroup H timeAxis}{V:Type*}[AddCommGroup V][Module ℂ V]
variable (B:Carton S V)(J:JMap V)(u:Remembers B J)
local notation "D"=> radial S
local notation "G"=> bands S
local notation "R"=> B.station
local notation "L"=> B.joinT
local notation "F'"=> B.pointGrade
local notation "Θ"=> B.retreat
local notation "ε"=> B.citizen
open WView Palette
variable {F:InkWaves V}{W:WView V}(g:InkPort B F W)(K:Courts V)(m:K.Carriage F){n:ℕ}
noncomputable abbrev voice (p:MarkWords V) : Module.End ℂ (ε):= (p.map (fun x:MarkType V=> B.pointMap x.1 x.2)).prod
noncomputable abbrev pointRoot:= B.evaluate []
lemma through_title(x y:MarkWords V): B.voice (x++y)=B.voice x * B.voice y:=by simp only [voice,List.map_append,List.prod_append]
lemma spoken (p x:MarkWords V):B.voice p (B.evaluate x)=B.evaluate (p++x):=by
 induction p with
 | nil=> rfl
 | cons i p e=> change B.pointMap i.1 i.2 (B.voice p (B.evaluate x))= _; rw [e]; rfl
noncomputable def null: Submodule ℂ V:= LinearMap.ker B.pointMap
lemma null_iff (x:V) : x∈ B.null↔ ∀ f:Test4,B.pointMap x f=0:=⟨fun e f=>DFunLike.congr_fun (LinearMap.mem_ker.mp e) f,fun p=> LinearMap.mem_ker.mpr (LinearMap.ext p)⟩
noncomputable abbrev acknowledged:= LinearMap.range B.pointMap
noncomputable def project : V →ₗ[ℂ] B.acknowledged:= LinearMap.rangeRestrict B.pointMap
lemma null_compares {x y:V}: B.project x=B.project y ↔ B.pointMap x=B.pointMap y:= ⟨fun p=> congrArg (fun i:B.acknowledged => i.val) p, fun p=> Subtype.ext p⟩
lemma claim_blank{v:V}:B.project v=0↔v∈B.null:= ⟨fun h=> LinearMap.mem_ker.mpr (show B.pointMap v=0 from (by
   have e:= congrArg (fun i:B.acknowledged=>i.val) h; exact e)), fun h=>Subtype.ext (LinearMap.mem_ker.mp h : B.pointMap v=0)⟩
-- W version of label detection: matches exact Carton map when B carries this measure.
variable (C:V)
include g
lemma blank_observed (e: C∈ B.null)(v:Fin n→V)(i:Fin n)(h:v i=C): W.W n v=0:=by
 have u(f:Fin n→Test4): W.W n v (Joint.materialize n f)=0:=by
    let x:Fin n→MarkType V:= fun i=>(v i,f i); obtain ⟨a,b,t⟩:= List.append_of_mem (List.mem_ofFn.mpr ⟨i,rfl⟩ : x i ∈ List.ofFn x); rw [show W.W n v _=W.expect (List.ofFn x) from (W.expect_ofFn x).symm, t, B.literal_price F W g]; have hu:B.evaluate (a ++ x i :: b)=0:=by
       rw [← B.spoken]; change B.voice a (B.pointMap (v i) (f i) (B.evaluate b))= _; rw [h,(B.null_iff _).1 e,LinearMap.zero_apply,map_zero]
    rw [hu]; exact inner_zero_right _
 apply ContinuousLinearMap.ext_on (R₁:=ℂ) (s:=Set.range (Joint.materialize n))
 · intro x; change x∈(Submodule.span ℂ (Set.range (Joint.materialize n))).topologicalClosure; rw [Work.C25.answer n]; exact Submodule.mem_top
 rintro _ ⟨p,rfl⟩; exact u p
include u
lemma blank_spins (e:∀ n (v: Fin n→V), C∈Set.range v→ W.W n v=0): C∈ B.null:=by
 apply (B.null_iff _).2; intro f; apply B.buds_pt _ _; intro x; rw [← eval,LinearMap.zero_apply]; apply Subtype.ext; apply (B.charged_iff).2; intro i; rw [Submodule.coe_zero,inner_zero_right]; change inner ℂ (B.evaluate i).1 (B.evaluate _).1=0; rw [← B.literal_gram J F W g u]; unfold WView.kernel; let y(t:MarkWords V): MarkWords V:=wordRev J t ++ (C,f)::x; unfold WView.expect; let k(p: Fin (y i).length):= ((y i).get p).1; have hs:C∈Set.range k:=by
    have he : (C,f)∈ (y i):=by unfold y; simp
    rw [← List.ofFn_get (y i),List.mem_ofFn] at he; obtain ⟨v,h⟩:=he; exact ⟨v,congrArg (Prod.fst) h⟩
 change W.W _ k _=0; rw [e _ k hs]; rfl
include m
/-- Equivalent condition involving only physically fixed real mark charges, with all *generic* poses,
  not necessarily even rotations or smoothness tested in reaching null comparisons.
  But the theorem needs already-earned relativistic estimate P (last checkpoint).
-/
lemma photograph_iff : C∈ B.null ↔ ∀ n:ℕ, ∀ v:Fin n→V,C∈ Set.range v→ ∀ p:Points n,p∈ generic n→ p∈Wheeled n→ F.entrance p v=0:=by
 refine ⟨fun t n v e x h y=> ?_,fun g'=> blank_spins B J u g C fun n v h=> Palette.all_unseen_zero v g.region g.level (fun x p=>Palette.on_wheel v g.region (fun _=>0) continuousOn_const (g' n v h) p)⟩
 obtain ⟨a,h⟩:=e; exact Palette.holding (WView.spectrum_paid g m) (B.blank_observed g C t _ a h) x y
omit u in
lemma photograph_blank (e:C∈B.null)(v:Fin n→V)(t:C∈Set.range v)(p:Points n)(hp:p∈conf n): helio K F n p v=0:=by
 refine Palette.preserving m g.region v (fun _ _=>0) p hp (fun r x h=>?_ ) (fun _=> continuousOn_const) (fun _=>rfl); obtain ⟨i,c⟩:=t; exact Palette.holding (WView.spectrum_paid g m) (B.blank_observed g C e _ (r.symm i) (by simpa [comp_apply] using c)) x h
lemma nulled_rotate (r:Ortho)(pr:Lorentz.properTurn r)(e:C∈ B.null): K.eu r C∈ B.null:=by
 apply (B.photograph_iff J u g K m _).2; intro n v h p t q; let M:Frames n:=(r⁻¹,1); rw [← helio_local m g.region p q, ←helio_carries m g.region M (Courts.proper_inv pr) p]
 apply B.photograph_blank g K m C e _ _ _ (frame_in M (wheel_at q)); obtain ⟨a,h⟩:=h; refine ⟨a,?_⟩; change K.eu r⁻¹ (v a)= C; rw [h]; exact K.eu_back r pr C
omit g m
lemma nulled_star (e:C∈ B.null): J C∈ B.null:=by
 apply (B.null_iff _).2; intro f; let X:MarkType V:= (C,Probe.bar f); have h:= B.meets_adj J u X; ext1 z; apply Subtype.ext; apply (B.charged_iff).2; intro i; rw [LinearMap.zero_apply,Submodule.coe_zero,inner_zero_right];
 have p:= B.FormalSharp J u X (B.evaluate i) z; change inner ℂ (B.pointMap C _ _).1 z.val=inner ℂ (B.engaged i) (B.pointMap (J C) (Probe.bar (Probe.bar f)) z).1 at p; rw [bar_twice, (B.null_iff _ |>.1 e),LinearMap.zero_apply, Submodule.coe_zero, inner_zero_left] at p; exact p.symm
variable (U: Action B.station)(h:B.Joins K U)
omit u
include h
lemma nulled_transport (r:Lorentz)(e:C∈ B.null): K.mi r C∈ B.null:=by
 apply (B.null_iff _).2; intro f; ext1 z; let p:=motion r; let y:=B.liftV K U h p⁻¹ z
 have hp:B.liftV K U h p y=z:=by apply Subtype.ext; exact (show U.V p (U.V p⁻¹ z.val)=z.val from (by simpa using U.goes p⁻¹ z.val))
 let q:= Joint.push p⁻¹ f; have hq:Joint.push p q=f:=by
   unfold q; ext1 x; rw [Joint.push_at,Joint.push_at,inv_inv,Poincare.emerges]
 have he:=B.withGuest K U h (C,q) p y
 change B.liftV K U h p (B.pointMap C q y)=B.pointMap (K.mi r C) (Joint.push p q) _ at he; rw [(B.null_iff _ |>.1 e),LinearMap.zero_apply,map_zero,hp,hq] at he; exact he.symm
omit h
include u
lemma noWaste (e: C∈ B.null) (f:Test4) : B.chalet J u C f=0:=by
 -- adjoint extension, on Θ. no graph-density assumption.
 ext1 v; apply Subtype.ext; apply (B.charged_iff).2; intro x; rw [LinearMap.zero_apply,Submodule.coe_zero,inner_zero_right]; let z:=B.evaluate x; change inner ℂ (B.reclaim z).1 _= _; rw [B.back_charm J u (C,f)]; change inner ℂ (B.pointMap (J C) (Probe.bar f) z).1 v.val=0; rw [(B.null_iff (J C)).1 (B.nulled_star J u _ e),LinearMap.zero_apply, Submodule.coe_zero]; exact inner_zero_left _
-- use with useful budgets on family R. Retain same maps. Do not assert Eu-label positivity or no-null before quotient.
omit u
noncomputable def survivors : B.acknowledged →ₗ[ℂ] Test4 →ₗ[ℂ] (ε→ₗ[ℂ] ε):= (B.acknowledged).subtype
lemma dispatched (x:V): B.survivors (B.project x)= B.pointMap x:=rfl
lemma detected (x:B.acknowledged)(e:x≠0): ∃ f:Test4, B.survivors x f≠0:=by
 by_contra! h; exact e (Subtype.ext (LinearMap.ext (show ∀ f:Test4, x.val f=(0:Test4→ₗ[ℂ] (ε→ₗ[ℂ] ε)) f from h)))
end YM.SatinWFixed.Carton
