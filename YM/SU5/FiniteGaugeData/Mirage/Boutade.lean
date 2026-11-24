import YM.SU5.FiniteGaugeData.Mirage.Stance
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 380000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy.Quest
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Heat Brique Window.Brique Journey Py Py.Rate LocalLimit Preparation FullBill Steam Vale
namespace Chaperone
variable {p q d J v:ℕ}{o:Cover}{N:Side}{w b e a:ℝ}
section mask
variable (p q d J)
abbrev Manor:= estate (p+d+J+10) (q+d+J+10)
abbrev WoodV:= estate p q
abbrev GrainV:= estate (p+d) (q+d)
abbrev FieldV : Finset (Face ℤ):=(estate (p+d+J+4) (q+d+J+4)) ×ˢ univ
def heartU(S:Finset Cover):= (S ×ˢ (univ:Finset Axis)).filter fun i:Edge Cover=> i.1+step i.2∈ S
variable (T: Chart o)
local notation "V₁"=> FieldV p q d J
local notation "V₂"=> GrainV p q d
local notation "UΞ"=> WoodV p q
local notation "Pξ"=> Manor p q d J
abbrev totals(f: LinksC):ℝ:= ∑ i∈ V₁, SU.group.chord (faceValue f i)
abbrev weightμ(f:LinksC):ℝ:= ∑ i∈heartU (GrainV p q d),SU.group.chord (gauge (T.rootF f) f i)
def scaleμ (a x:ℝ):= max 0 (min 1 (2-x/a))
lemma scale_cost (a x:ℝ): 0 ≤ scaleμ a x ∧ scaleμ a x ≤1:=⟨le_max_left ..,max_le zero_le_one (min_le_left ..)⟩
lemma scalePop (u:0<a) (t:b ≤ a) : scaleμ a b=1:= by unfold scaleμ; rw [min_eq_left,max_eq_right zero_le_one]; linarith only [show b/a≤1 from div_le_one_of_le₀ t u.le]
lemma scaleNow (u:0<a)(p:scaleμ a b≠0): b ≤2*a:=by by_contra! h; apply p; unfold scaleμ; rw [max_eq_left]; exact (min_le_right ..).trans (by linarith only [show 2< b/a from (lt_div_iff₀ u).mpr h])
def drawMask (a:ℝ)(f:LinksC):ℂ:= (scaleμ a (totals p q d J f+weightμ p q d T f):ℝ)
lemma tall : Continuous (totals p q d J):=by unfold totals; apply continuous_finsetSum; intro i x; unfold faceValue; fun_prop
lemma short : Continuous (weightμ p q d T):=by unfold weightμ; apply continuous_finsetSum; intro i h; unfold Chart.rootF Lattice.gauge; fun_prop
lemma charmC : Continuous (drawMask p q d J T a):=by unfold drawMask scaleμ ; refine Complex.continuous_ofReal.comp ?_; refine continuous_const.max (continuous_const.min (continuous_const.sub (((tall p q d J).add (short p q d T)).div_const a)))
lemma root_gauge (x:Cover→SU.E)(W:LinksC)(i:Edge Cover): gauge (T.rootF (gauge x W)) (gauge x W) i=x o*(gauge (T.rootF W) W i)*(x o)⁻¹:=by unfold Lattice.gauge Chart.rootF; change travel (gauge x W) o _ * _ *_= _ * (travel W o _*_*_)*_; rw [travel_gauge]; change x o*travel W o _*_ * _*(travel (gauge x W) o _)⁻¹=_; rw [travel_gauge,T.endsT,T.endsT]; group
lemma nativeGuardC : GaugeInvariant (drawMask p q d J T a) := by intro t W; unfold drawMask weightμ totals; simp_rw [root_gauge,face_gauge, SU.group.chord_conj]
lemma gramS : GrainV p q d⊆ Manor p q d J := ownM (by omega) (by omega)
lemma grain_in : WoodV p q ⊆ GrainV p q d:=ownM (by omega) (by omega)
variable (g:Chart.Hires (GrainV p q d) (Manor p q d J) o T)
lemma flags_roof : carpet (FieldV p q d J)⊆ Manor p q d J:=by
 intro x h; obtain ⟨i,h,t⟩:= mem_biUnion.mp h; let v:=square i.2.val.1 i.2.val.2; obtain hz:= own_walk (mem_product.mp h|>.1) v (List.mem_toFinset.mp (show x∈ (visits i.1 v).toFinset from t)); exact ownM (by rw [show v.length=4 from rfl]; omega) (by rw [show v.length=4 from rfl]; omega) hz
include g
lemma charmLocal : Lattice.LocalOn (Manor p q d J) (drawMask p q d J T a):=by
 intro V W t; unfold drawMask; let h:= gramS p q d J; let F' : Agrees (GrainV p q d) V W:= fun i x y=>t i (h x) (h y)
 have hs: Agrees (GrainV p q d) (gauge (T.rootF V) V) (gauge (T.rootF W) W):= by
    intro i v t'; unfold Lattice.gauge; rw [show T.rootF V i.1= T.rootF W i.1 from T.rent g i.1 v _ _ t,F' i v t', show T.rootF V (i.1+step i.2) = T.rootF W (i.1+step i.2) from T.rent g _ t' _ _ t] -- `rent` t has H argument
 have hw: totals p q d J V= totals p q d J W:=sum_congr rfl fun i u=>by
    apply congrArg SU.group.chord; let G:=flags_roof p q d J; apply travel_local i.1 (square i.2.val.1 i.2.val.2) V W (fun i' p v=> t i' (G (mem_biUnion.mpr ⟨i,u,List.mem_toFinset.mpr p⟩)) (G (mem_biUnion.mpr ⟨i,u,List.mem_toFinset.mpr v⟩)))
 rw [hw,show weightμ p q d T V= weightμ p q d T W from (by unfold weightμ; exact sum_congr rfl fun i t=> congrArg SU.group.chord (hs i (mem_product.mp (mem_filter.mp t).1).1 (mem_filter.mp t).2))]
variable (X: Side)(u:Hosp (Manor p q d J) X)
def areaH : Corset (region (WoodV p q) X) (region (Manor p q d J) X) (wrap (More X) o):= Chart.passH T u ((grain_in p q d).trans (gramS ..)) (fun i t=> g i ((grain_in ..) t))
include u
lemma port_value (V:Pane X) (i:Cover)(v:i∈ GrainV p q d) : (areaH p q d J T g X u).g V (wrap (More X) i)= T.rootF (onC X V) i := Chart.tenor_site T i ((gramS p q d J) v) u V
omit u -- omit X? include u only not X
-- transfer estimates
include g
lemma Ticket_shape (X:Side)(V:Pane X) (z: drawMask p q d J T a (onC X V) ≠0)(eq:0 < a): ∀ i:admiss X,i.1∈region (estate (p+d+J+4) (q+d+J+4)) X→ SU.group.chord (faceValue V i) ≤ 2*a:=by
 rintro ⟨x,i⟩ h; obtain ⟨y,v,rfl⟩:=mem_image.mp h; rw [show faceValue V _= faceValue (onC X V) (y,i) from press_face (y,i) (V,V)]
 have he:totals p q d J (onC X V)+weightμ p q d T (onC X V)≤2*a:= scaleNow eq (fun h=> z (by unfold drawMask; rw [h,Complex.ofReal_zero])) -- cast form z reducible?
 exact (single_le_sum (f:=fun i=>SU.group.chord (faceValue (onC X V) i)) (fun i _=>Gaugen _ i) (mem_product.mpr ⟨v,mem_univ _⟩)).trans ((le_add_of_nonneg_right (sum_nonneg (fun i _=>SU.group.chord_nonneg _))).trans he)
where Gaugen (V:LinksC)(i:Face ℤ):0≤ SU.group.chord (faceValue V i):= SU.group.chord_nonneg _
lemma glowC (X:Side)(W:Orbit X)(P0:Loom X)(b y:ℝ)(u:0<a)(h:2*a≤b)(H:Roof X b y J P0)(z: drawMask p q d J T a (onC X W.1) ≠ 0): Agrees (region (GrainV p q d) X) W.1 (P0 W):=by
 intro i u' v; symm; apply H.lamp; apply Finset.disjoint_left.mpr; intro x f g'; obtain ⟨o',t',e⟩:= (RG.flags_spec ..).1 f; apply e.not_ge; apply le_trans _ h; apply Ticket_shape p q d J T g X W.1 z u o'; apply own_halo X 4; obtain ⟨v1,z,r⟩:= halo_spec.mp g';
 refine halo_spec.mpr ⟨x,own_halo X J (halo_spec.mpr ⟨v1,(show ends i⊆region (GrainV p q d) X from insert_subset_iff.mpr ⟨u',singleton_subset_iff.mpr v⟩) z,r⟩),?_⟩; rw [separation_comm]; exact Extra.Iteration.Shapes.visits_dist _ _ _ (List.mem_toFinset.mp t')
omit g
lemma draw_norm(b:ℝ)(x:LinksC): ‖drawMask p q d J T b x‖≤1:=by unfold drawMask; rw [Complex.norm_real,Real.norm_of_nonneg (scale_cost b _|>.1)]; exact (scale_cost b _).2
private lemma plusK(a:Axis):(step a:Cover)∈ estate 1 1:=by refine (own _).mpr fun i=>?_ ; unfold zoneL; by_cases h:i=a <;> simp [step_apply,h]
include u
private lemma knows' {x:Cover}(y:x∈GrainV p q d)(t:Axis)(m:wrap (More X) x+step t∈ region (GrainV p q d) X): x+step t∈ GrainV p q d:=by
 have he:x+step t∈ Manor p q d J:=ownM (by omega) (by omega) (own_add y (plusK t)); obtain ⟨z,p',q⟩:= mem_image.mp m; refine u.seat_ ((gramS ..) p') he ?_ ▸ p'; rw [map_add,wrap_step,q]
include g
lemma danceC (z:Pane X)(x:drawMask p q d J T a (onC X z)≠0)(i:Seat X)(j:Axis)(p' : (i,j)∈ leaks (region (GrainV p q d) X)) (e:0<a): SU.group.chord ((Lattice.gauge ((areaH p q d J T g X u).g z) z) (i,j))≤2*a:=by
 obtain ⟨x',v,rfl⟩:= mem_image.mp ((mem_filter.mp p').2.1); let y:= x'+step j; let G:= (areaH p q d J T g X u).g z; let I':=onC X z; let P':= weightμ p q d T I'; let U:=SU.group.chord (gauge (T.rootF I') I' (x',j)); have hvP:x'∈ GrainV p q d:= v; have hx:= knows' p q d J X u hvP j ((mem_filter.mp p').2.2); unfold Lattice.gauge; rw [port_value p q d J T g X u z _ hvP,←wrap_step, ←map_add, port_value p q d J T g X u z _ hx,← show onC X z ((x',j): Edge Cover)=z (wrap (More X) x',j) from onC_spec X z _]; change U≤ _
 have he:totals p q d J I'+P'≤2*a:= scaleNow e (fun h=>x (by unfold drawMask; unfold P' I' at h; rw [h,Complex.ofReal_zero]))
 exact (single_le_sum (a:=(x',j)) (f:=fun i=> SU.group.chord (gauge (T.rootF I') I' i)) (fun i _=>SU.group.chord_nonneg _) (mem_filter.mpr ⟨mem_product.mpr ⟨v,mem_univ _⟩,hx⟩)).trans ((le_add_of_nonneg_left (sum_nonneg fun i _=> SU.group.chord_nonneg _)).trans he)
omit u
lemma PurchaseC (C:ℝ)(e:0<b) (z:0 < C): ∃ a:ℝ, 0<a ∧ ∀ (X:Side)(W:Loom X)(u:Hosp (Manor p q d J) X){y:ℝ}, Roof X b y J W → CashMask (areaH p q d J T g X u) (drawMask p q d J T a ∘ onC X) (region (GrainV p q d) X) C W:=by
 let m:ℕ:= (GrainV p q d).card*4+1; have hm:0<(m:ℝ):=Nat.cast_pos.mpr (by unfold m; omega); let v:=C/(2*m); have hv:0<v:=div_pos z (by positivity); have he:{x:SU.E| ‖brand x-1‖≤v}∈𝓝 (1:SU.E):=(show Continuous fun x:SU.E=> ‖brand x-1‖ from (Dial.spinD.sub continuous_const).norm).continuousAt.eventually (ge_mem_nhds (by simpa only [brand_one,sub_self,norm_zero] using hv))
 obtain ⟨t,h,pT⟩:=Next.Rank.surrounds SU.group _ he; let a:=min t b/2; have hA:0<a:=half_pos (lt_min h e); refine ⟨a,hA,fun X W u y tallP=>⟨?_,fun x p'=>?_,fun x h'=>glowC p q d J T g X x W b y hA ?_ tallP h'⟩⟩
 · refine ⟨(charmC p q d J T).comp (on_cont X),fun x y h=>charmLocal p q d J T g _ _ (on_agree X h),fun x=>draw_norm ..,fun t x=>?_⟩; exact (congrArg _ (Chart.gauge_here t x)).trans (nativeGuardC _ _ _ _ T _ _)
 · let U:=region (GrainV p q d) X; let V:=Lattice.gauge ((areaH p q d J T g X u).g x) x; change Tulip.fare _ (profile V) _ ≤ _; have hV:∀ i∈ leaks U,‖brand (V i)-1‖ ≤ v:=fun i z=> pT ((danceC p q d J T g X u x p' i.1 i.2 z hA).trans (by unfold a; linarith only [min_le_left t b]) : SU.group.chord (V i)≤ t) -- actually weak.C ≤ t no lt.
   have hU:(U.card:ℝ)*4 ≤ m:=by exact_mod_cast ((Nat.mul_le_mul_right 4 (card_image_le (s:=GrainV p q d) (f:=wrap (More X)))).trans (Nat.le_succ _)) -- f argument
   exact (Peaks.payment V (profile V) v v (by simpa using hv) U hV).trans (((mul_le_mul_of_nonneg_right ((Peaks.leak_size U).trans hU) (by positivity : 0≤v+v))).trans_eq (by unfold v; field_simp; ring))
 unfold a; linarith [min_le_right t b] -- t shadow adjust
-- gives event exact `Mark`
omit g
lemma subsidize (e:0<a): ∃ (A:Finset (Face ℤ))(v:ℝ),0<v ∧∀ b:ℝ,b≤v→∀ f:LinksC, ¬alarm A b (f,f) → drawMask p q d J T a f=1:=by
 let Z(f:LinksC):= totals p q d J f+weightμ p q d T f; have hf:Continuous Z:=(tall p q d J).add (short p q d T); have hg(t:LinksC)(v:PureZ t): Z t=0:=by unfold Z totals weightμ; rw [v.owns]; simp [v]
 obtain ⟨A,b,z,H⟩:=pension hf hg a e; exact ⟨A,b,z,fun v p' x t'=>by unfold drawMask; rw [scalePop e (H v p' x t'),Complex.ofReal_one]⟩
end mask
#print axioms PurchaseC
#print axioms charmLocal
#print axioms subsidize
end Chaperone
end YM.CF.Buffered.Afterglow.Hierarchy.Quest
