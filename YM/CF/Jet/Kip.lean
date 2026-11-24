import YM.CF.Jet.Degree
set_option autoImplicit false
noncomputable section
namespace YM.CF.Jet
open Function Filter Metric Lat Finset Tenant Branch Fock Dial MeasureTheory Phase Phase.Sample Lattice Cube Broc Drapes Tulip Peaks Brace Paige Rush
open scoped Topology Matrix BigOperators ContDiff NNReal Matrix.Norms.L2Operator InnerProductSpace
set_option synthInstance.maxSize 8000
attribute [local instance] opCStarAlgebra
variable {L B:Side}
lemma zen (n:ℕ)(K:ℝ)(hK:0≤K)(L:Side): ∃ C:ℝ,K≤C∧∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E]{N P:Side}(G:Ratio N P),G.count=L→∀ (U:E→Bkg (More P))(X:E→Stun N)x,TransK n U x K →seek X n x K→ seek (fun i=>ascend G (X i) (U i)) n x C:=by
 obtain ⟨D,t,H⟩:=factor_is hK n (4*L.val)
 let a:=max D K; obtain ⟨C,g,h⟩:= compact_allow n (show 0≤a from le_max_of_le_right hK) _ (act_is n)
 refine ⟨max K (composeCost n C a),le_max_left ..,fun E _ _ _ _ G ht U X x p P i=> ?_⟩
 let f(t:E):=(SU.fund (travel (U t) i (dart G i)),hook (X t) ((ratio G).parent i)); have hf:Allows n f x a:= ((H _ _ _ _ p i (dart G i) (by rw [← ht]; exact dartK ..)).mono (le_max_left ..)).pair ((P _).mono (le_max_right ..)); exact ((h (f x) hf.value).comp hf).mono (le_max_right ..)
variable {j:ℕ}{ho:Odd L.val}{T:Script Male}{Y:Pricing j L ho T}{e:ℝ}{m r:Side}(g:Grasp Y B e)(he:0<e)(n:ℕ){K:ℝ}
def LineE (n:ℕ)(G:Ratio (CSide m B) (CSide r B))(K e:ℝ): Draw (Rent0 G e):= ⟨fun E _ _ _ V f=>∀ x∈ V,TransK n (fun i=>(f i).val.1) x K ∧ TransK n (fun i=>(f i).val.2) x K⟩
def SparY (n:ℕ)(G:Ratio (CSide m B) (CSide r B))(K e:ℝ): Draw (Gift0 G (e:=e)):= ⟨fun E _ _ _ V f=>∀ x∈ V,TransK n (fun i=>(em G (f i)).val.1) x K ∧ TransK n (fun i=>(em G (f i)).val.2) x K ∧ ToR n (fun i=>(f i).val.2) x K⟩
lemma pureZ (n:ℕ)(K:ℝ)(B:Side)(h:1≤K):∃ C:ℝ,0≤C∧∀ m r:Side,∀ e:ℝ,∀ G:Ratio (CSide m B) (CSide r B), Inspired (LineE n G K e) (opensD G e) (SparY n G K e) C n:=by
 obtain ⟨C,c,H⟩:= ryth n K B h; refine ⟨C,c,fun m r e G=> ⟨c,fun E _ _ _ V p f u=> H m E V p (fun i=>(f i).val.2) (fun x t=>(u x t).2),?_⟩⟩
 intro E _ _ _ V W l v w q Q F t s x hx
 obtain ⟨T,A⟩:=Q x (l hx)
 refine ⟨fun i=> (T i).germ ?_,fun i=>(A i).germ ?_,fun i=> (allows_const _ ((vote_unit (t i)).le.trans h)).germ ?_⟩
 · filter_upwards [w.mem_nhds hx] with y hy; exact (congrArg (fun x=>SU.fund (x.1.val.1 i)) (s y hy)).symm
 · filter_upwards [w.mem_nhds hx] with y hy; exact (congrArg (fun x=>SU.fund (x.1.val.2 i)) (s y hy)).symm
 filter_upwards [w.mem_nhds hx] with y hy; exact (congrArg (fun x=>(x.2 i).val) (s y hy)).symm
include he
lemma conductor (K:ℝ)(hK:1≤K):∃ a w:ℝ, 0<a∧0<w∧∀ (m r:Side) (G:Ratio (CSide m B) (CSide r B)),G.count=L→g.roundZ≤(CSide m B).val→∀ M, Screen (dressL G e) (LineE n G K e) n (fun i=>flakeL g G i.val M) a w:=by
 obtain ⟨D,hD,H⟩:= star_cost n (zero_le_one.trans hK) B; have hp:0≤D:= zero_le_one.trans (hK.trans hD)
 obtain ⟨C,hC,Q⟩:=zen n D hp L; obtain ⟨w,u,P⟩:=interior_work g n ((hK.trans hD).trans hC)
 let V:=feeG (popV L B); have ht:0<V:=by unfold V feeG; positivity
 obtain ⟨v,hv,hF⟩:=pureZ n K B hK; obtain ⟨s,f,h⟩:=stash v hv n (div_pos (twist_pos g) ht)
 refine ⟨twistRate g/V/2,max 1 (s*(V*w)), half_pos (div_pos (twist_pos g) ht),lt_max_of_lt_left zero_lt_one, fun m r G hc k M=>?_⟩
 let b:=s
 letI : CompactSpace ↑(Rent0 G e):=open_tr ..
 let X:= bliss (e:=e) G; let ff:=talc g G hc k he
 have hp:0<popV L B:= (mul_pos (show 0<4 by decide) L.property) |>.trans_le (Nat.le_add_right ..)
 let F:= fun x:AcreZ m r g G=> firmL g G x.val M -Matrix.trace (eExp T Y.k M G (post x.val));
 have ho: Screen X.botL (SparY n G K e) n (F ∘ ff) (twistRate g/V) (V*w):=by
    apply Screen.leaps (Q:=ridQ g n G C) (Ω:=SparY n G K e) (c:=X.botL) (b:=bunchS g G) (v:=V) (w:=V) (Φ:=foam _ (popV L B)) (P G hc k M) (foams _ hp _) ff (talc_c g G hc k he) u (div_nonneg (twist_pos g).le ht.le) (by rw [div_mul_cancel₀ _ ht.ne']) ?_ ?_ ?_
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
    · intro x y; refine ⟨y,Subtype.ext ?_⟩; let S:=(scaleG G y); let P:=x.val.1.val; let Q:= (starfish m B P.2 x.val.2);
      change accordL G (july G y P) (starfish m B (gauge S P.2) (partner m B S x.val.2))=frost G y (accordL G P Q)
      rw [starG g.capY he.le x.val.1.property.cg (law_rich m B _ _ x.property) S]; exact Prod.ext rfl (Prod.ext (ascent_g G P.1 y Q) rfl)
    intro E _ _ _ V t f p x hx; obtain ⟨h₁,h₂,h₃⟩:=p x hx
    let U:=f x; have hU:=U.val.1.property
    have hY : seek (hatchL G ∘ f) n x D:=H E _ _ _ x h₂ h₃ e _ he.le hU.cg (law_rich m B _ _ U.property) g.capY
    exact ⟨fun i=> (h₁ i).mono (hD.trans hC),fun i=> (h₂ i).mono (hD.trans hC),Q E G hc _ _ x (fun i=> (h₁ i).mono hD) hY, fun i=> (hY i).mono hC⟩
 have he (R:Broc.Table r B): (SupA G R).card≤R.card:= (rate_cap _).trans (cloud_count G R)
 have hT:= screen_mean X (hF m r e G) ho he (fun S x=> (complex_down m B (cloudG G S):Down _ _)) (fun S x y p=> trans_t G x y S p) (fun S x=>⟨fun _ _ _=>rfl,fun _ _ _=>rfl⟩) f (fun T v p=> h _ p _ _ (he _))
 apply Screen.reserve (le_refl _) (le_max_right 1 (s*(V*w)))
 convert hT using 1; funext x; unfold means flakeL; apply integral_congr_ae; apply Eventually.of_forall; intro i
 let T:= opensD G e; by_cases h:fall (T x) i≠0
 · exact congrArg (fun z:ℂ=>fall (T x) i • z) ((sampler_p (A:=T) (F ∘ ff) (x,i) h).symm)
 rw [not_not] at h; change fall (T x) i • _=fall (T x) i • _; rw [h,zero_smul,zero_smul]
end YM.CF.Jet
