import YM.CF.Broc.Mint
/-! Integrate all phases as one local scalar. (Topological version) -/
set_option autoImplicit false
set_option synthInstance.maxSize 8000
noncomputable section
namespace YM.CF.Broc
open Function Filter Lattice Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Paige Phase Phase.Sample Brace Cube Peaks Tulip Rush Drapes
open scoped Topology Matrix BigOperators Matrix.Norms.L2Operator InnerProductSpace
attribute [local instance] opCStarAlgebra
variable {j:ℕ}{L: Side}{ho:Odd L.val}{T:Script Male}{Y:Pricing j L ho T}{B m r: Side}{e:ℝ}
variable (g:Grasp Y B e)(G: Ratio (CSide m B) (CSide r B))(hc:G.count=L)(k:g.roundZ ≤(CSide m B).val)(he:0<e)
def opensD(G: Ratio (CSide m B) (CSide r B))(e:ℝ)(x:Rent0 G e):Plan (Index m) cloud:= rock m B x.val.2
abbrev SupA(G:Ratio (CSide m B) (CSide r B))(S:Table r B):=complexA m B (cloudG G S)
def bliss :Lit (opensD G e) (dressL G e) (SupA G) where
 pollen p := (pass m B (scaleG G p)).toMeasurableEquiv
 level p :=rain_g _ _ (scaleG G p)
 gauge x t p:= law_g _ _ x.val.2 t (scaleG G p)
 phase:= by
   let X:= fun x:Rent0 G e×Cue m=> (x.1.val.2,x.2)
   have hp: Continuous X := (continuous_snd.comp (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd
   let f := fun t:Skin m B× Cue m=>law m B t.1 t.2
   change Continuous (f ∘ X); exact (show Continuous f from law_cont ..).comp hp
 spread:=fun S T h=> complex_up m B (cloud_grows G h)
abbrev Gift0:= Sam (opensD G e)
lemma trans_t (x y: Rent0 G e)(S: Table r B)(p:(dressL G e).rel S x y)(t): sails (opensD G e x) (SupA G S) t=sails (opensD G e y) (SupA G S) t:=by
 apply prod_congr rfl; intro i g
 have ht: room m B i⊆cloudG G S:= (mem_filter.mp g).2; exact water_limit _ _ i t t (fun _ _=> rfl) (fun a u v=> p.2 a (ht u) (ht v))
abbrev em(x:Gift0 (e:=e) G):=x.val.1
abbrev hatchL (x: Gift0 (e:=e) G) := starfish m B (em _ x).val.2 x.val.2 -- tune em args
def talc (hc:G.count=L)(k:g.roundZ ≤(CSide m B).val)(he:0<e)(x: Gift0 (e:=e) G):AcreZ m r g G:=⟨accordL G x.val.1.val (hatchL G x),pose_g g he G hc k _ x.val.1.property _ (starK g.capY he.le x.val.1.property.cg (law_rich m B _ _ x.property))⟩ -- section parameters hx dependencies not type!
include hc k he
lemma talc_c: Continuous (talc g G hc k he):=by
  apply Continuous.subtype_mk; let L(x: Gift0 (e:=e) G):= (em _ x).val; have hL :Continuous L:=continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
  have hx:Continuous (hatchL (e:=e) G):=by
    let f(x: Gift0 (e:=e) G):=(x.val.1.val.2,x.val.2); have he':Continuous f:= (continuous_snd.comp hL).prodMk (continuous_snd.comp continuous_subtype_val)
    exact (starfish_c (m:=m) g.capY he.le).comp_continuous (f:=f) he' fun x=>⟨x.val.1.property.cg, law_rich m B _ _ x.property⟩
  exact hL.prodMk (((ascent_c G).comp (hx.prodMk (continuous_fst.comp hL))).prodMk hx)
lemma opas (M:Male) :Seat (dressL G e) (fun i=> flakeL g G i.val M) (inkp g/feeG (popV L B)) (feeG (popV L B)*inkg g):=by
  letI : CompactSpace ↑(Rent0 G e):=open_tr ..
  let X:= bliss (e:=e) G; let f:=talc g G hc k he -- tune
  let V:= feeG (popV L B); have ht:0<V:=by unfold V feeG; positivity
  have hp:0<popV L B:= (mul_pos (show 0<4 by decide) L.property) |>.trans_le (Nat.le_add_right ..)
  let F:= fun x:AcreZ m r g G=> firmL g G x.val M -Matrix.trace (eExp T Y.k M G (post x.val));
  have hv: Seat X.botL (F ∘ f) (inkp g/V) (V*inkg g):=by
    apply Seat.shop (c:=X.botL) (b:=bunchS g G) (Φ:=foam _ (popV L B)) (v:=V) (w:=V) (foams _ hp _) (brink g G hc k M) f (talc_c g G hc k he) (inkp_price g).le (div_nonneg (ink_pos g).le ht.le) (by rw [div_mul_cancel₀ _ ht.ne'])
    · intro S x y h; let H:=foam _ (4*G.count.val) S; let K:= foam _ (popV L B) S
      have hb:S⊆H:=foam_in ..; have hk:H⊆K:=by
        intro i hi; obtain ⟨v,g,p⟩:=mem_biUnion.mp hi
        exact mem_biUnion.mpr ⟨v,g,(bay_mem _).mpr (((bay_mem _).mp p).trans (hc.symm ▸ (Nat.le_add_right (4*G.count.val) (G.count.val*(8*B.val)))))⟩ -- tune dep
      have hh: foam _ (8*B.val) (cloudG G H) ⊆cloudG G K:= by unfold K; rw [←hc]; exact acorn G 0 B S
      have ht:AgreeF (cloudG G H) (hatchL G x) (hatchL G y):=honor _ _ _ (h.2.less (complex_up _ _ hh)) (fun i v p=>h.1.2 i (hh v) (hh p))
      refine ⟨fun i v p=>h.1.1 i (hk (hb v)) (hk (hb p)), fun i v p=> h.1.2 i (cloud_grows G (hb.trans hk) v) (cloud_grows G (hb.trans hk) p),fun i hi=> ?_, ht.less (cloud_grows G hb)⟩
      let p:=visits i (dart G i)
      have hm (x) (l:x∈p): x∈ K :=hk (mem_biUnion.mpr ⟨i,hi,(bay_mem _).mpr ((visit_v _ _ _ l).trans (dartK ..))⟩)
      let R:=ratio G
      have hc':R.parent i ∈ cloudG G H:= Finset.mem_filter.mpr ⟨mem_univ _,mem_biUnion.mpr ⟨i,hi,(bay_mem _).mpr ((parentsN R i).trans (show G.count.val≤ _ by omega))⟩⟩
      change ascend G _ _ i = ascend G _ _ i; unfold ascend; rw [ht _ hc']; congr 1; exact travel_local _ _ _ _ (fun i a b=> h.1.1 i (hm _ a) (hm _ b))
    intro x y; refine ⟨y,Subtype.ext ?_⟩; let S:=(scaleG G y); let P:=x.val.1.val; let Q:= (starfish m B P.2 x.val.2);
    change accordL G (july G y P) (starfish m B (gauge S P.2) (partner m B S x.val.2))=frost G y (accordL G P Q)
    rw [starG g.capY he.le x.val.1.property.cg (law_rich m B _ _ x.property) S]; exact Prod.ext rfl (Prod.ext (ascent_g G P.1 y Q) rfl)
  have hT:=X.loot hv (SupA G) (fun x T=> (complex_down m B (cloudG G T):Down _ _)) (fun x=> subset_refl _) (fun S x y p=> trans_t G x y S p)
  convert hT using 1; funext x; unfold means flakeL; apply integral_congr_ae; apply Eventually.of_forall; intro i
  let T:= opensD G e; by_cases h:fall (T x) i≠0
  · exact congrArg (fun z:ℂ=>fall (T x) i • z) ((sampler_p (A:=T) (F ∘ f) (x,i) h).symm)
  rw [not_not] at h; change fall (T x) i • _=fall (T x) i • _; rw [h,zero_smul,zero_smul]
end YM.CF.Broc
