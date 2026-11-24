import YM.SU5.FiniteGaugeData.Steam.Gauss
import YM.SU5.FiniteGaugeData.Brique.Sentry
import YM.Next.RANK.Ray

set_option autoImplicit false
set_option quotPrecheck false
set_option maxHeartbeats 460000
set_option synthInstance.maxSize 22000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin Window.Brique Heat
open Reed (Fine)
attribute [local instance] opCStarAlgebra
-- `open Next.Rank.Spindle` ? shadow other `Word` etc. prefer qualified
open Next.Rank
open scoped Classical
variable {r n d m g h w:ℕ} {x o y:Cover}{N:Side}
variable (A: Finset (Face ℤ))(t B:ℝ)(o:Cover) (K:Calibration)
private def shield₁ (t v:ℝ): ℝ := max 0 (min 1 (2-v/t))
private lemma shield_t (t x:ℝ) : 0≤ shield₁ t x ∧ shield₁ t x ≤ 1:= ⟨le_max_left .., max_le zero_le_one (min_le_left ..)⟩
private lemma lodge (t:ℝ):Continuous (shield₁ t):= by unfold shield₁; fun_prop
private abbrev tariffH(V:LinksC)(i:Face ℤ):= SU.group.chord (faceValue V i)
def bedH (V:LinksC):ℂ:= ((∏ i∈A, shield₁ t (tariffH V i)):ℝ)
lemma bedH_bound (U:LinksC):‖bedH A t U‖≤1:=by unfold bedH; rw [Complex.norm_real,Real.norm_of_nonneg (prod_nonneg (fun i _=>(shield_t t _).1))]; exact prod_le_one (fun i _=>(shield_t t _).1) (fun i _=>(shield_t t _).2)
lemma bedH_cont: Continuous (bedH A t) := by unfold bedH; refine Complex.continuous_ofReal.comp ?_; refine continuous_finsetProd A fun i h=> (lodge t).comp ?_; unfold tariffH faceValue; fun_prop
lemma bedH_local : Lattice.LocalOn (carpet A) (bedH A t):=by
 intro x y v; unfold bedH; apply congrArg ((↑):ℝ→ℂ); apply Finset.prod_congr rfl; intro i p; rw [show tariffH x i=tariffH y i from congrArg SU.group.chord (travel_local i.1 (square i.2.val.1 i.2.val.2) _ _ (fun e h k=>v e (mem_biUnion.mpr ⟨i,p,List.mem_toFinset.mpr h⟩) (mem_biUnion.mpr ⟨i,p,List.mem_toFinset.mpr k⟩)))]
variable {A t}
lemma bed_works {U:LinksC}(p:0<t)(q:bedH A t U ≠ 0):∀ i∈ A, tariffH U i ≤ 2*t:=by
 intro i h; by_contra! v; apply q; have hv:2 < tariffH U i/t := (lt_div_iff₀ p).mpr v; have ht:shield₁ t (tariffH U i)=0:=by unfold shield₁; have hz:= min_le_right (1:ℝ) (2-tariffH U i/t); rw [max_eq_left]; linarith
 unfold bedH; rw [Finset.prod_eq_zero h ht, Complex.ofReal_zero]
lemma bed_lords {U:LinksC}(p:0<t)(q:¬alarm A t (U,U)): bedH A t U=1:=by
 have ht:∀ i∈A, shield₁ t (tariffH U i)=1:=fun i hi=> by
    have hx:= div_le_one_of_le₀ (le_of_not_gt (show ¬t<tariffH U i from (fun h=>q ⟨i,hi,h⟩))) p.le
    unfold shield₁; rw [min_eq_left (by linarith),max_eq_right zero_le_one]
 unfold bedH; rw [Finset.prod_eq_one ht, Complex.ofReal_one]
variable (A t)
def umbrella := scalar K (bedH A t ∘ Prod.fst) -- explicit order?
lemma bower : InTest K false (carpet A) false (umbrella A t K):=.seed (.fromC _ _ (bedH_cont ..) (bedH_local A t))
lemma roof_line (m:Side)(x:Fields (K.c m)): ‖umbrella A t K m x‖ ≤ 1:=by unfold umbrella scalar; simpa using bedH_bound A t (onC _ x.1)
lemma harsh_w (q:0<t)(p:B≤ t) : (troubles K A B)*(1-umbrella A t K)=1-umbrella A t K:=by
 funext m x; let u:=onC _ x.1; by_cases h:alarm A B (u,u); swap
 · have hv:umbrella A t K m x=1:=by unfold umbrella scalar; dsimp only [Function.comp_apply]; rw [bed_lords q,one_smul]; rintro ⟨i,t',e'⟩; exact h ⟨i,t',p.trans_lt e'⟩
   simp [hv]
 simp only [troubles,scalar,Pi.mul_apply,strike]; rw [if_pos (show alarm A B (onC _ x.1,onC _ x.2) from h),one_smul,one_mul]
section
variable (n₀ A₀ J:ℕ)(m:Side)
local notation "S"=> scape o (sphereR n₀ J) -- n₀ Inn base
local notation "ô"=> wrap (More m) o
def carpetB : Finset (Face ℤ) := (scape o (n₀+J+4)) ×ˢ univ
local notation "τ" => carpetB o n₀ J
lemma sap_marks : carpet τ ⊆ S:=by
 intro a p; obtain ⟨q,u,r⟩:= mem_biUnion.mp p; let P:=square q.2.val.1 q.2.val.2; have hx:q.1∈ scape o (n₀+J+4):=(mem_product.mp (show q∈(scape o (n₀+J+4)) ×ˢ univ from u)).1; apply scape_mono (r:=n₀+J+4+P.length) _ (vision_box (u:=P) hx (List.mem_toFinset.mp r)); rw [show P.length=4 from rfl]; unfold sphereR; omega
lemma sap_frost (W:Pane m)(i:admiss m)(hx:i.1∈region (scape o (n₀+J+4)) m)(p:0<t)(q:bedH τ t (onC m W) ≠ 0): SU.group.chord (faceValue W i) ≤ 2*t:= by
 obtain ⟨x,f⟩:=i; obtain ⟨y,r,rfl⟩:=mem_image.mp (show x∈region _ m from hx); rw [show faceValue W _= faceValue (onC m W) (y,f) from press_face (y,f) (W,W)]; exact bed_works p q (y,f) (mem_product.mpr ⟨r,mem_univ _⟩)
local notation "ζ"=> scape o n₀
lemma sap_fare (p:0<t)(h:2*(n₀+1)<(More m).val)(W:Pane m)(q:bedH τ t (onC m W) ≠ 0) (z:Spindle.Dim (ô) n₀): SU.group.chord (Spindle.spine W (ô) z) ≤ (4*n₀)*(2*t):=by
 rw [Spindle.spun W (ô) h z]; let a:=Spindle.word SU.group h z; refine (Spindle.played_cost a _ (by positivity:(0:ℝ)≤2*t) (fun i=>?_)).1.trans (mul_le_mul_of_nonneg_right ?_ (by positivity));
 · rw [Spindle.registering n₀ W h]; unfold Spindle.spine; rw [face_gauge,SU.group.chord_conj]; apply sap_frost t o n₀ J m W _ _ p q; refine image_subset_image (scape_mono (r:=n₀) (show n₀≤n₀+J+4 by omega)) ?_; change _ ∈ region (scape o n₀) m; rw [spindle_PATCH]; exact Spindle.village_le _ (Spindle.faceOrigin i)
 exact_mod_cast Spindle.lengths_word SU.group h z
-- release sickness. paid bridge `.F`. cutoff exact. need Θ landmark cap. (Ctor requires locale on T⊆ S; choose S Price & T where gauge acts). `mask radius` fixes support after s.
variable {T R : Finset Cover}
def coveredB (D:Finset Cover)(x:T⊆scape o n₀)(v: scape o n₀⊆ D) : Corset (region T m) (region D m) (ô) where
 g W := Spindle.fingers W (ô)
 up_cont:=by apply continuous_pi; intro i; unfold Spindle.fingers Spindle.leaves expandAt; fun_prop
 locale i h:=by
    let N:=More m; let o':= (ô); have hv:i∈Spindle.patch n₀ o':=spindle_PATCH .. ▸ image_subset_image x h -- type Eq direction?
    let u:=Lattice.lift (i-o'); have hg:u∈Lattice.box n₀:= Work.E08.lift_mem_box ((Spindle.doors ..).1 hv); intro U V e; unfold Spindle.fingers Spindle.leaves; dsimp only;
    have he : Agrees ↑(Spindle.patch n₀ o') U V:= agrees_mono e (show Spindle.patch n₀ o'⊆region D m from (spindle_PATCH ..) ▸ image_subset_image v)
    have ha : Agrees (Lattice.box n₀) (expandAt o' U) (expandAt o' V) :=by
       rintro ⟨x,i⟩ p r; apply he (Spindle.edgeAt x o' i) (Spindle.village_le x p); have hz:=Spindle.village_le (o:=o') (x+step i) r; rw [map_add,wrap_step,add_right_comm] at hz; exact hz
    exact travel_local (0:Cover) (Spindle.paths u) _ _ (fun j p r=> ha j (Spindle.village _ hg _ p) (Spindle.village _ hg _ r))
 law t W:=by funext i; unfold Spindle.fingers Spindle.leaves; simp only [expandAt_gauge, travel_gauge,map_zero,zero_add, Spindle.stops, wrap_lift,sub_add_cancel]; rfl
lemma glowB (W:Orbit m)(P:Loom m){b y:ℝ}(p:0<t)(h:2*t≤b)(H:Roof m b y J P)(q:bedH τ t (onC m W.1) ≠0): Agrees (region (scape o n₀) m) W.1 (P W):= by
 intro i u v; symm; apply H.lamp; apply Finset.disjoint_left.mpr; intro x f g; obtain ⟨o',t',e⟩:= (RG.flags_spec ..).1 f; apply e.not_ge; apply le_trans _ h; apply sap_frost t o n₀ J m W.1 o' _ p q; apply halo_walk (n₀+J) 4 o m
 obtain ⟨a,z,r⟩:= halo_spec.mp g; refine halo_spec.mpr ⟨x,halo_walk n₀ J o m (halo_spec.mpr ⟨a,(show ends i⊆region (scape o n₀) m from insert_subset_iff.mpr ⟨u,singleton_subset_iff.mpr v⟩) z,r⟩),?_⟩
 rw [separation_comm]; exact Extra.Iteration.Shapes.visits_dist _ _ _ (List.mem_toFinset.mp t')
lemma exceedsB : ζ⊆S:= scape_mono (by unfold sphereR; omega)
private lemma outfit : Stump (region S m) (bedH τ t ∘ onC m) := by
 refine ⟨(bedH_cont ..).comp (on_cont m), fun x y h=> bedH_local τ t _ _ (on_agree m (agrees_mono h (Finset.image_subset_image (sap_marks o n₀ J)))),fun x=>bedH_bound ..,?_⟩
 intro x V; unfold bedH; dsimp only [Function.comp_apply]; apply congrArg ((↑):ℝ→ℂ); apply Finset.prod_congr rfl; intro i _; unfold tariffH; exact congrArg (shield₁ t) (by rw [←press_face i (gauge x V,V),←press_face i (V,V),face_gauge,SU.group.chord_conj]) -- tune
lemma healthB {b y:ℝ}(x:T⊆scape o n₀)(C:ℝ)(z:0<C)(g:0<b): ∃ t:ℝ, 0<t ∧ ∀ v:ℝ,0<v → v ≤ t → ∀ (m:Side), 2*(n₀+1)<(More m).val → ∀ P, Roof m b y J P → CashMask (coveredB o n₀ m (scape o (sphereR n₀ J)) x (exceedsB o n₀ J)) (bedH (carpetB o n₀ J) v ∘ onC m) (region (scape o n₀) m) C P := by
 let G:=SU.group; let Bβ:ℕ:=(n₀+n₀+1)^4*4; have hΛ:0<Bβ:=(by unfold Bβ; positivity); let a:=C/(2*(Bβ:ℝ)); have ha:0<a:=div_pos z (by positivity)
 have he:{x:SU.E| ‖brand x-1‖≤a}∈𝓝 (1:SU.E):=(show Continuous fun x:SU.E=> ‖brand x-1‖ from (Dial.spinD.sub continuous_const).norm).continuousAt.eventually (ge_mem_nhds (by simpa only [brand_one,sub_self,norm_zero] using ha)) -- tune
 obtain ⟨R,hR,r⟩:=Next.Rank.surrounds SU.group _ he; let b':ℝ:=b/2; let ε:= R/(8*n₀+1); have hv:0<ε:=div_pos hR (by positivity)
 refine ⟨min ε b',lt_min hv (half_pos g),fun v hi hv m h P p=> ⟨outfit v o n₀ J m, fun i hι => ?_, fun i p'=>glowB v o n₀ J m i P hi ?_ p p'⟩⟩
 · let W:= Spindle.spine i (wrap (More m) o); rw [spindle_PATCH]; let T₀:=Spindle.patch n₀ (wrap (More m) o); change fare T₀ (profile W) 1≤_
   have hm: v ≤ ε:= le_trans hv (min_le_left ..); have hθ:v*(8*n₀+1)≤R:= (le_div_iff₀ (by positivity)).mp hm; have hu: ∀ j∈ leaks T₀, ‖brand (W j)-1‖ ≤ a:=fun j t=>by
       refine r (show SU.group.chord _ ≤ R from ?_); exact (sap_fare v o n₀ J m hi h i hι ⟨j,t⟩).trans (by linarith only [hi,hθ]); -- tune
   have ht: (leaks T₀).card ≤ Bβ:= Spindle.broad (wrap (More m) o) _; have hp: (Bβ:ℝ)*(a+a)=C:=by unfold a; field_simp; ring -- tune
   exact (Peaks.payment W (profile W) a a (by simpa using ha) T₀ hu).trans ((mul_le_mul_of_nonneg_right (show ((leaks T₀).card:ℝ) ≤ (Bβ:ℝ) by exact_mod_cast ht) (by positivity)).trans hp.le)
 have hx:v≤b/2:= hv.trans (min_le_right ..); linarith
lemma shield_equality (T T₀:Support (More N)) (o:Seat N)(t:Corset T T₀ o) : cargo t (bedH A B ∘ onC N) 1 = (fun x:Fields N=>bedH A B (onC N x.1) • 1):= funext fun x=>by unfold cargo; rw [flips_one]; rfl
end
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
