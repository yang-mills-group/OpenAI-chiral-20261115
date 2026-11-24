import YM.SU5.Registration.Momenta.SectorBudget
import YM.SU5.Registration.Rasp.PitchJet
/-!
 # Retreat: all energy smooth vectors in this sector in the same field domain here.
 All budgets unchanged as functions (obtains topology-relative costs at inherited G budget).
 Extends Mink spacelike & Lor covariance on this dense invariant domain with even interpolation
 through positive allowances (after width).
-/
set_option autoImplicit false
noncomputable section
namespace YM.SatinWFixed.Carton
open Function Set Filter MeasureTheory Measure Complex Submodule SatinRegistration
open Boundary Probe Mink Mink.Poincare Multiplier Roy Spectral OS.Semigroup SatinEdge.RealSheet
open CF.Buffered.Afterglow.Hierarchy.Seld
open CF.Buffered.Afterglow.Hierarchy.Seld.Poin
open scoped Topology NNReal ENNReal BigOperators InnerProductSpace ComplexOrder
variable {H:Hilbert}{S: _root_.YM.OS.Semigroup H timeAxis}{V:Type*}[AddCommGroup V][Module ℂ V]
variable (B:Carton S V)(J:JMap V)(u:Remembers B J)
local notation "D"=> radial S
local notation "G"=> bands S
local notation "Q"=> B.pointShelf
local notation "R"=> B.station
local notation "L"=> B.joinT
open SatinRegistration.Grading
local notation "F'"=> B.pointGrade
abbrev retreat:= B.pointGrade.domain
local notation "Θ"=> B.retreat
local notation "ε"=> B.citizen
noncomputable def charm : B.retreat→ₗ[ℂ] radial S:= {
 toFun x:= ⟨x.val.val,(B.prices_root _).1 x.prop⟩
 map_add' x y:=rfl
 map_smul' c x:=rfl }
lemma enchanted : Injective B.charm:= fun a b h=> Subtype.ext (Subtype.ext (congrArg (fun y:D=>y.val) h))
@[simp] lemma charm_cast (x: B.retreat) : (B.charm x).1=x.val.val:=rfl
lemma pays_charm (x: B.retreat)(k:ℕ): (G).budget k (B.charm x).1=(F').budget k x.val:= (B.operates_honest _ _).symm
lemma retreat_approach {ι:Type*}(l:Filter ι)(Y:ι→ B.retreat)(x:B.retreat) : (G).Approaches l (fun i=> B.charm (Y i)) (B.charm x) ↔ (F').Approaches l Y x:=by
 have h(i k): (G).budget k ((B.charm (Y i)).val-(B.charm x).val)= (F').budget k ((Y i).val-x.val):=by
   have he:=B.pays_charm (Y i-x) k; rw [map_sub] at he; exact he
 unfold Grading.Approaches; simp_rw [h]
noncomputable def invited(x:D)(p:x.val∈Q): Θ:= ⟨⟨x.val,p⟩,(B.prices_root _).2 x.prop⟩
lemma charm_invited(x:D)(p:x.val∈Q): B.charm (B.invited x p)=x:=rfl
lemma chartered(x:B.retreat): (B.charm x).val∈ Q:=x.val.prop
lemma citizens: ε≤ Θ:= fun x p=> (B.prices_root _).2 (B.live ⟨x,p⟩).prop
abbrev reclaim : B.citizen→ₗ[ℂ] B.retreat:= Submodule.inclusion B.citizens
lemma charm_reclaims(p:B.citizen) : B.charm (B.reclaim p)=B.live p:=rfl
include u
noncomputable def clearAt (x:V)(f:Test4):B.retreat →ₗ[ℂ] B.retreat:= {
 toFun y:= B.invited (B.black x f (B.charm y)) (B.light_invariant J u (x,f) (B.charm y) (B.chartered y))
 map_add' y z:= B.enchanted (by simp only [map_add]; rfl)
 map_smul' c z:=B.enchanted (by simp only [map_smul]; rfl) }
noncomputable def chalet : V →ₗ[ℂ] Test4 →ₗ[ℂ] (B.retreat→ₗ[ℂ] B.retreat):= {
 toFun x:= {
   toFun f:= clearAt B J u x f
   map_add' f g:= LinearMap.ext (fun y=> B.enchanted (by
     rw [LinearMap.add_apply,map_add]; exact LinearMap.congr_fun (map_add (B.operator x) f g) (B.charm y)))
   map_smul' c f:= LinearMap.ext (fun y=> B.enchanted (by rw [LinearMap.smul_apply,map_smul]; exact LinearMap.congr_fun (map_smul (B.operator x) c f) (B.charm y))) }
 map_add' x y:= by ext1 f; ext1 z; apply B.enchanted; rw [LinearMap.add_apply,LinearMap.add_apply,map_add B.charm]; exact LinearMap.congr_fun (DFunLike.congr_fun (map_add B.operator x y) f) (B.charm z)
 map_smul' c x:= by ext1 f; ext1 z; apply B.enchanted; rw [LinearMap.smul_apply,LinearMap.smul_apply,map_smul B.charm]; exact LinearMap.congr_fun (DFunLike.congr_fun (map_smul B.operator c x) f) (B.charm z) }
local notation "T'"=> B.chalet J u
lemma issues(t:MarkType V)(x:B.retreat): B.charm ((B.chalet J u) t.1 t.2 x)= B.activate t (B.charm x):=rfl
lemma reaches_in (t:MarkType V)(x:B.citizen): B.reclaim (B.pointMap t.1 t.2 x)= B.chalet J u t.1 t.2 (B.reclaim x):= rfl
lemma charm_formal (t:MarkType V)(x y:B.retreat) : inner ℂ ((B.chalet J u) t.1 t.2 x).val y.val=inner ℂ x.val ((T') (J t.1) (Probe.bar t.2) y).val:=by
 change inner ℂ (B.activate t (B.charm x)).1 (B.charm y).1= _; exact B.sharp J u t ..
lemma chalet_cont (x:B.retreat)(t:V): Continuous (fun f=> ((T') t f x).1):= Continuous.subtype_mk (B.black_con t (B.charm x)) _
omit u
noncomputable def thaw (s:ℝ≥0): Θ →ₗ[ℂ] Θ:={
 toFun x:= B.invited (stoveAt S s (B.charm x)) (B.warmMoves s _ (B.chartered x))
 map_add' a b:= B.enchanted (by simp only [map_add]; rfl)
 map_smul' c a:= B.enchanted (by simp only [map_smul]; rfl) }
lemma thaws (s:ℝ≥0)(x:Θ) : B.charm (B.thaw s x)= stoveAt S s (B.charm x):=rfl
lemma thaw_zero : B.thaw 0=LinearMap.id:=by ext1 i; apply B.enchanted; rw [thaws,LinearMap.id_apply,stoveAt_zero]
include u
noncomputable def melts (x:V)(f:Test4)(s:ℝ≥0): Θ →ₗ[ℂ] Θ:= ((B.thaw s).comp ((T') x f)).comp (B.thaw s)
lemma melted (x:V)(f:Test4){s:ℝ≥0}(h:0<s)(y:B.retreat): B.charm (B.melts J u x f s y)= B.blue x s f (B.charm y):=by rw [B.blue_stove x s h]; rfl
lemma melted_0 (x:V)(f:Test4) : B.melts J u x f 0=(T') x f:= by rw [melts, B.thaw_zero]; rfl
variable {ι:Type*}{y:B.retreat}{X:ι→ B.retreat}
lemma melts_approach (l:Filter ι)(s:ι→ℝ≥0)(hX:B.pointGrade.Approaches l X y) (h:Tendsto s l (𝓝[>] 0))(x:V)(f:Test4): (F').Approaches l (fun i=> B.melts J u x f (s i) (X i)) (T' x f y):=by
 apply (B.retreat_approach l _ _).1; intro k; refine (B.blue_finish x f l s h ((B.retreat_approach l X y).2 hX) k).congr' ((h.eventually self_mem_nhdsWithin).mono (fun i p=> ?_)); dsimp only; rw [←B.melted J u x f p]; rfl
omit u in
lemma thaws_budget (l:Filter ι)(s:ι→ℝ≥0)(hX:B.pointGrade.Approaches l X y) (t:ℝ≥0)(h:Tendsto s l (𝓝 t)) : (F').Approaches l (fun i=> B.thaw (s i) (X i)) (B.thaw t y):=by
 apply (B.retreat_approach l _ _).1; exact through_heat S l _ h ((B.retreat_approach l X y).2 hX)
variable {n:ℕ}(v: Fin n→V)(f:Fin n→Test4)(C:List (Fin n))(N:Fin n→ Fin n→ℝ≥0)
lemma through_rooms (l:Filter ι)(hX:B.pointGrade.Approaches l X y) (S':ι→Fin n→ℝ≥0)(h:∀ i,Tendsto (fun x=> S' x i) l (𝓝[>] 0)) (t:ι→Fin n→Fin n→ℝ≥0)(p:∀ i j,Tendsto (fun k=>t k i j) l (𝓝 (N i j))) :
 (F').Approaches l (fun i=> (Film (fun j=> B.melts J u (v j) (f j) (S' i j)) (fun j k=> B.thaw (t i j k)) C) (X i)) (Film (fun j=> B.chalet J u (v j) (f j)) (fun j k=> B.thaw (N j k)) C y):=by
 induction C with
 | nil=>exact hX
 | cons a C ih=>
    cases C with
    | nil=> exact B.melts_approach J u l _ hX (h a) (v a) (f a)
    | cons b C=> let Z:ι→ Θ := fun i=> Film (fun j=> B.melts J u (v j) (f j) (S' i j)) (fun j k=> B.thaw (t i j k)) (b::C) (X i)
                 let z₀:Θ:= Film (fun j=> B.chalet J u (v j) (f j)) (fun j k=> B.thaw (N j k)) (b::C) y
                 exact B.melts_approach J u l _ (B.thaws_budget (X:=Z) (y:=z₀) l _ ih _ (p a b)) (h a) (v a) (f a)
noncomputable def ritual (x:V) (f:Test4) : R →ₗ.[ℂ] R:= ⟨Θ,(Θ).subtype.comp (B.chalet J u x f)⟩
lemma adj_true (t:MarkType V): B.ritual J u (J t.1) (Probe.bar t.2) ≤ (B.ritual J u t.1 t.2).adjoint:= LinearPMap.IsFormalAdjoint.le_adjoint (F').grade_dense (B.charm_formal J u t)
lemma closedC (t:V)(f:Test4): (B.ritual J u t f).IsClosable:=by
 let Y':= B.ritual J u (J t) (Probe.bar f); let A:= (B.ritual J u t f); have h':A.IsFormalAdjoint Y':= B.charm_formal J u (t,f); exact (LinearPMap.adjoint_isClosed (F').grade_dense).isClosable.leIsClosable (h'.symm.le_adjoint (F').grade_dense) -- Lean inference
lemma invo (s:MarkType V) : opTag J (opTag J s)=s:= Prod.ext (u.both _) (bar_twice s.2)
lemma back_charm (t:MarkType V)(x y:B.retreat) : inner ℂ x.val ((B.chalet J u) t.1 t.2 y).val=inner ℂ ((B.chalet J u) (J t.1) (Probe.bar t.2) x).val y.val:=by
 let s:=opTag J t; have he:= B.charm_formal J u s x y; change _ = inner ℂ x.val ((B.chalet J u) (opTag J s).1 (opTag J s).2 y).val at he; rw [B.invo J u t] at he; exact he.symm
variable {F:InkWaves V}{W:WView V}(g:InkPort B F W)(K:Courts V)(m:K.Carriage F)
include g m
lemma regional_ritual (x y:V) (f g':Test4)(h:Fields.causal f g')(a:B.retreat) : (B.chalet J u) x f ((B.chalet J u) y g' a) = (B.chalet J u) y g' ((B.chalet J u) x f a):=by
 refine Subtype.ext ((B.charged_iff).2 (fun i=>?_)); let z:= B.evaluate i; let w:= B.reclaim z; change inner ℂ w.val _=inner ℂ w.val _
 rw [B.back_charm J u (x,f), B.back_charm J u (y,g'), B.back_charm J u (y,g'), B.back_charm J u (x,f)] -- occ. tested intentions
 rw [← reaches_in B J u (opTag J (x,f)),← reaches_in B J u (opTag J (y,g')),← reaches_in B J u (opTag J (y,g')), ← reaches_in B J u (opTag J (x,f)),← B.regional J g u m _ _ _ _ (show Fields.causal (Probe.bar f) (Probe.bar g') from (by rw [Fields.causal,bar_reach f, bar_reach g']; exact h))]
omit g m
variable (U:Action B.station) (p:B.Joins K U)(j:K.Parley J)
omit u
include p
noncomputable def escort (r:Poincare): B.retreat →ₗ[ℂ] B.retreat:= (U.V r).toLinearMap.restrict (p:=Θ) (q:=Θ) (fun x u=> (B.important U (B.unanimous_time K U p).symm (B.real_cone K U p) r x u).1)
lemma escort_paid (r:Poincare)(x:Θ) : (B.escort K U p r x).val=U.V r x.val:=rfl
lemma march (r:Poincare)(x:ε): B.escort K U p r (B.reclaim x)=B.reclaim (B.liftV K U p r x):= rfl -- prop defeq
omit p in
lemma alt (x y:B.station)(p:Poincare) : inner ℂ x (U.V p y)=inner ℂ (U.V p⁻¹ x) y:=by
   rw [← U.flavor p⁻¹ x,U.goes]
lemma withGuest (s:MarkType V)(r:Poincare)(z:ε): B.liftV K U p r (B.pointMap s.1 s.2 z)=B.pointMap (K.foreign r s).1 (K.foreign r s).2 (B.liftV K U p r z):= LinearMap.congr_fun (B.fields_covariant K U p r s.1 s.2) z
-- boost covariance relation with all radial-budget smooth vectors.
include j u
lemma boots (s:MarkType V)(r:Poincare)(x:B.retreat) : B.escort K U p r ((T') s.1 s.2 x)= T' (K.foreign r s).1 (K.foreign r s).2 (B.escort K U p r x):=by
 let t:=K.foreign r s
 have he:K.foreign r⁻¹ (opTag J t)=opTag J s:=by unfold t; rw [K.stars_foreign J j,← K.foreign_comp,inv_mul_cancel,K.foreign_one]
 refine Subtype.ext ((B.charged_iff).2 (fun i=>?_)); let z:=B.evaluate i; let w:=B.liftV K U p r⁻¹ z
 let q:=opTag J s; let q':= opTag J t
 change inner ℂ (B.reclaim z).val (U.V r (T' s.1 s.2 x).val) =_ -- toStation fix below
 rw [B.alt U]; change inner ℂ (B.reclaim w).val _= inner ℂ (B.reclaim z).val (T' t.1 t.2 _).val
 rw [B.back_charm J u s, B.back_charm J u t]
 -- now higher inner with chamber on left; pay real price using hidden relation. no assertion radial core dense in graph needed
 change inner ℂ (B.pointMap q.1 q.2 w).val x.val=inner ℂ (B.pointMap q'.1 q'.2 z).val (U.V r x.val)
 rw [B.alt U]; change _= inner ℂ (B.liftV K U p r⁻¹ (B.pointMap q'.1 q'.2 z)).val _; rw [B.withGuest K U p q',he]
end YM.SatinWFixed.Carton
open YM.SatinWFixed
#print axioms Carton.adj_true
#print axioms Carton.through_rooms
#print axioms Carton.boots
#print axioms Carton.regional_ritual
