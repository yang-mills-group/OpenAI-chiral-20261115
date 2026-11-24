import YM.SU5.FiniteGaugeData.Maypole.Optic
/-! # Other perspectives, tilt and all shifted mixed prices (no new star hypothesis) -/
set_option autoImplicit false
set_option maxHeartbeats 340000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp.Tufa
open Function Filter Metric Set MeasureTheory OS OS.Semigroup Mink General Lorentz
open scoped Topology BigOperators NNReal InnerProductSpace ComplexOrder
open Poin Celeritas Land Leal Breve Poin.Gem Boundary Probe Flute
variable {ι:Type}{K:Axis→Hilbert}(W:∀ a:Axis,OS.Semigroup (K a) a)(G:Canopy (K timeAxis) ι)(Ω:(i:Axis)→ (K i).space)
local notation "a"=>timeAxis
local notation "S"=> W timeAxis
local notation "Z"=> Ω timeAxis
open Folio Canopy
variable (u:SO)(b:Axis)(x:E4)
-- sends b→a. exists proper even when just directional pivot. Temporal and spatial spect PATTERN dual Eu signs. no star req across orientations.
abbrev Reigns(u:SO)(b:Axis):=forall x:E4,walk u.val x timeAxis=x b
lemma InMeets : ∃ u:SO, Reigns u b:=by
 by_cases t:b=timeAxis; · subst b; exact ⟨1,fun _=>rfl⟩
 obtain ⟨s,h⟩:= Fin.exists_castSucc_eq.mpr (show b≠ Fin.last 3 from t); let e:= Ray.fromAxis s; let r:= -(Real.pi/2); refine ⟨Flute.moveB e r,fun x=>?_⟩; change time (Flute.circleB e r x)=_; rw [Flute.ttake]; simp [r,e,h]
abbrev feel(u:SO):E4 →L[ℝ] E4:= walk u.val
lemma feel_h (x:E4): feel u (feel u⁻¹ x)=x:= General.retrace ..
lemma fee_h (x:E4): feel u⁻¹ (feel u x)=x:= General.proceeds ..
lemma Vnorm(u:SO)(x:E4): ‖feel u x‖=‖x‖:= u.property.2 x
lemma Ving(u:SO)(x y:E4): inner ℝ (feel u x) (feel u y) = inner ℝ x y := (show E4 →ₗᵢ[ℝ] E4 from { (feel u).toLinearMap with norm_map':=Vnorm u }).inner_map_map x y
variable (h:Reigns u b)
include h
lemma holds_basis : feel u (basis b)=basis a:=by
 apply ext_inner_right ℝ; intro y; nth_rw 1 [← feel_h u y]; rw [Ving, _root_.YM.basis_inner, _root_.YM.basis_inner]; exact (h ((feel u⁻¹) y)).symm.trans (congrArg (fun x:E4=> x a) (feel_h u y))
lemma boosty: feel u ((SEP b x).val)=(SEP a (feel u x)).val:=by change feel u (x-x b • basis b)=feel u x- (feel u x a) •basis a; rw [map_sub,map_smul,holds_basis u b h,h x]
lemma firmament: (feel u x) ∈ swingCone a ↔ x∈ swingCone b:= by change ‖((SEP timeAxis (feel u x)).val)‖≤ _ ↔ ‖(SEP b x).val‖ ≤_; rw [←boosty u b x h,Vnorm,h x]
section
variable (N:Tribe G)
lemma LineH(L:List (Item G.Chip)): Folio.ahead b L→Folio.ahead timeAxis (Marked G u L):=fun p=> List.pairwise_map.mpr (p.imp (fun {i j} p=> by change (walk u.val i.2) a<(walk u.val j.2) a; rw [h,h]; exact p)) -- ambiguity `ahead`
lemma FrontH(L:List (Item G.Chip))(p:LaneE b 0 L): LaneE timeAxis 0 (Marked G u L):= ⟨LineH G u b h L p.1, fun i z=> by obtain ⟨j,z₁,rfl⟩:= List.mem_map.mp z; change 0<walk u.val _ a; rw [h]; exact p.2 j z₁⟩
lemma TailH(L:List (Item G.Chip))(p:BackE b 0 L): BackE timeAxis 0 (Marked G u L):= ⟨LineH G u b h L p.1, fun i z=> by obtain ⟨j,z₁,rfl⟩:= List.mem_map.mp z; change walk u.val _ a <0; rw [h]; exact p.2 j z₁⟩
variable (F:Bench (W timeAxis))(p:F.val=Ω timeAxis)(q:∀ i:Axis,∀ x:E4,M (W i) x (Ω i)=Ω i)(V:Set (Shrine K))(g:Stamp W G N V)(π: b≠ timeAxis)(κ: ∀ n:ℕ,Gem.Prism W Ω V b n)(v:RotReal W G Ω N)
local notation "Κ"=>receiptI G N b
local notation "Fν"=>G.grade
local notation "Π"=> W b
local notation "T"=> Ω b
include κ g p q v
lemma stir (L:List (Item G.Chip))(z:Folio.ahead b L): wordValue (W b) (Ω b) (receiptI G N b) G.grade L= wordValue (W timeAxis) (Ω timeAxis) G.dep G.grade (Marked G u L):=by
 obtain ⟨n,f,x,rfl⟩:=e_pref L; let M:=Each n; have hv:ProofOrder x b M:=(order_p ..).1 z; let F':=tileR W G Ω F N p.symm v; have hh:= stirring x W G Ω F N V p.symm f M b v g (fun i=>rlock (W i) (Ω i) (q i)) (List.Perm.refl _) hv (Or.inr (κ n)) -- q needed arg
 have hu:Marked G u (mail x f M)=mail (turnO u.val x) (G.stampE u f) M:=by unfold Marked mail; rw [List.map_map]; rfl
 have ht:=LineH G u b h _ z; rw [hu] at ht ⊢; rw [peering, peering, ← p]; -- meanE Z scope; want HH
 rw [Gem.utop] at hh; exact hh.symm.trans ((G.fluent _ _ u _ _ F' (order_in x b _ (.refl _) hv)).trans (Canopy.sing G _ F _ _ M F' (.refl _) ((order_p ..).1 ht)))
abbrev lifeK(L:List (Item G.Chip))(L':List (Item G.Chip)):=(face (W timeAxis) Z G.dep Fν 0 (Marked G u L'), role (W timeAxis) Z G.dep Fν 0 (Marked G u L))
lemma glimmer (A B:List (Item G.Chip))(p':BackE b 0 A)(t: LaneE b 0 B)(hp:0≤x b) : inner ℂ (role (W b) T Κ Fν 0 A) (((W b).E (x b).toNNReal*(W b).U (SEP b x)) (face (W b) T Κ Fν 0 B))= inner ℂ ((lifeK W G Ω u A B).2) (((W timeAxis).E (x b).toNNReal*(W timeAxis).U (SEP timeAxis (feel u x))) ((lifeK W G Ω u A B).1)):= by
 let P:=feel u x; let L:=Marked G u A; let L':= Marked G u B; have hv:= TailH G u b h A p'; have ht:=FrontH G u b h B t; let z:=stir W G Ω u b h N F p q V g κ v (A++shifted x B) (aheadJoin x A B hp p' t); have hh: Marked G u (A++shifted x B)=L++ shifted P L':=by
    unfold L L' P Marked shifted; rw [List.map_append,List.map_map,List.map_map]; congr 2; funext v; apply Prod.ext; rfl; exact map_add ..
 have he:P timeAxis=x b:= h x
 rw [hh] at z; have hs:= rho_join (W timeAxis) Z (q a) G.dep G.grade P L L' (he ▸ hp) hv ht; rw [he] at hs; exact (rho_join (W b) T (q b) Κ Fν x A B hp p' t).trans (z.trans hs.symm)
end
-- Wick time continuation.He.R.Frame
section
variable {H H':Hilbert}(U:OS.Semigroup H b)(S':OS.Semigroup H' timeAxis)
--
variable (A B:H)(F G:H')
variable (ℓ:∀ x:E4,0≤ x b→ inner ℂ A ((U.E (x b).toNNReal*U.U (SEP b x)) B)=inner ℂ F ((S'.E (x b).toNNReal*S'.U (SEP timeAxis (feel u x))) G))
include h ℓ
lemma roamE : inner ℂ A (M U x B)=inner ℂ F (M S' (feel u x) G):=by
 let P:= U.U (SEP b x); let t:= x b; let Q:= S'.U (SEP a (feel u x))
 let X(z:ℂ):=inner ℂ A (Veil U z (P B)); let Y(z:ℂ):=inner ℂ F (Veil S' z (Q G))
 let W':=OS.Semigroup.inside; have hh(r:ℝ)(he:0<r): X (r:ℂ)=Y (r:ℂ):=by
    let v:= x+(r-t) • basis b; have hv:v b=r:=by simp [v,t];
    have hx:SEP b v=SEP b x:=by unfold v; rw [map_add,Haven.SEP_t,add_zero]
    have hU: SEP a (feel u v)= SEP a (feel u x):=by apply Subtype.ext; rw [←boosty u b v h,←boosty u b x h,hx]
    have q:= ℓ v (hv ▸ he.le); rw [hx,hv,hU] at q; unfold X Y; rw [veil_real,veil_real]; exact q -- ordering rw hv after hx term. tune
 let z:=sideways t; have hz: z∈closure W':=by
    let θ(i:ℝ):= (i:ℂ)+z; have he:Tendsto θ (𝓝[>] 0) (𝓝 z):= ((show Continuous θ from Complex.continuous_ofReal.add continuous_const).tendsto' 0 z (by simp [θ])).mono_left nhdsWithin_le_nhds; refine mem_closure_of_tendsto he ?_; filter_upwards [self_mem_nhdsWithin] with i p'; change 0< (θ i).re; simpa only [θ,z,Complex.add_re,Complex.ofReal_re,side,add_zero] using (Set.mem_Ioi.mp p')
 have hF {H:Hilbert}{A':Axis}(G:OS.Semigroup H A')(x y:H): AnalyticOnNhd ℂ (fun z=> inner ℂ x (Veil G z y)) OS.Semigroup.inside:= fun z p=> ((innerSL ℂ x).comp (ContinuousLinearMap.apply ℂ H.space y)).analyticAt _|>.comp (veil_analytic G p)
 have he: X z= Y z:=by
    apply EqOn.closure _ _ _ hz; rotate_left
    · exact (((innerSL ℂ A).continuous.comp (veil_C U id (fun _=>P B) continuous_id continuous_const)))
    · exact (((innerSL ℂ F).continuous.comp (veil_C S' id (fun _=>Q G) continuous_id continuous_const)))
    refine (hF U A (P B)).eqOn_of_preconnected_of_frequently_eq (hF S' F (Q G)) (convex_halfSpace_gt Complex.reCLM.toLinearMap.isLinear 0|>.isPreconnected) (z₀:=1) (show (1:ℂ)∈W' from (zero_lt_one : (0:ℝ) < 1)) ?_
    intro N; have ht: Tendsto ((↑):ℝ→ℂ) (𝓝[>] (1:ℝ)) (𝓝[≠] 1):= by
       have ht:Tendsto ((↑):ℝ→ℂ) (𝓝[>] (1:ℝ)) (𝓝[≠] (↑(1:ℝ):ℂ)):=by apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ Complex.continuous_ofReal.continuousAt.continuousWithinAt; filter_upwards [self_mem_nhdsWithin] with i v; exact fun g=> (mem_Ioi.mp v).ne' (Complex.ofReal_injective (show (i:ℂ)=_ from g))
       simpa using ht
    obtain ⟨i,u,p⟩:= ((ht.eventually N).and (show ∀ᶠ i:ℝ in 𝓝[>] (1:ℝ),1 < i from self_mem_nhdsWithin)).exists; exact u (hh i (lt_trans zero_lt_one p))
 change inner ℂ A (U.edge t (P B))= inner ℂ F (S'.edge _ (Q G)); rw [show feel u x timeAxis=x b from h x]; unfold X Y z at he; rw [Veil,Veil,side, Real.toNNReal_zero,U.eZero,S'.eZero,show (sideways t).im= -t from by simp [sideways],neg_neg] at he
 exact he
end
#print axioms roamE
end YM.CF.Buffered.Afterglow.Hierarchy.Seld.Vp.Tufa
