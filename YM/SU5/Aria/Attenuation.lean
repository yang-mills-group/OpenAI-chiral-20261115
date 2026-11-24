import YM.SU5.Aria.Dyad
/-!
# Simultaneous attenuation of ALL microscopic germs
No P-energy damping used. No assumption of separability of the labels (only the resulting
positive Hilbert spaces in this application). Actual sequence of distributions rather than
nets, thanks to strong topology on approximate hulls. (For a fixed tuple of requests, see
`dedication`; even without separability.)
-/
set_option autoImplicit false
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Aria
open Set Function Filter Metric
open Germ TopologicalSpace
open scoped Topology InnerProductSpace Classical
variable {Γ:AddSubgroup ℝ}{H:Hilbert}
abbrev Whisper (Γ:AddSubgroup ℝ) := Mist (↥Γ)
local notation "Wp"=> Whisper Γ
variable (P:Players Γ H)(D E: Whisper Γ)
abbrev aloof (r:ℝ)(D:Whisper Γ):Prop:= D.holds (fun i=>|(i:ℝ)| < r)
def tide : H.Op:= D.mean (P.play)
lemma tide_mean (x:H): tide P D x=D.mean (fun i=> P.play i x):=by induction (D:Mist (↥Γ)) with
 | point a=>rfl
 | midP a b i j=> unfold tide; rw [Mist.mean,Mist.mean,ContinuousLinearMap.smul_apply,ContinuousLinearMap.add_apply]; change (1/2:ℂ)•(tide P a x+tide P b x)=_; rw [i,j] -- D abbrev
lemma tide_le (x:H): ‖tide P D x‖≤‖x‖:=by rw [tide_mean]; exact D.mean_budget (fun i=>P.play i x) _ (D.solves _ fun t=> P.pulls t x)
lemma attenuates : ‖tide P D‖ ≤ 1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun i=> (by rw [one_mul]; exact tide_le ..)) -- wrong
lemma tide_contract (x y:H): dist (tide P D x) (tide P D y) ≤ dist x y:=by simp only [dist_eq_norm,←map_sub]; apply tide_le
lemma mist_of_hull {x y:H}{r:ℝ}(q:Players.hull Γ H P r x y): ∃ D:Whisper Γ, aloof r D ∧ tide P D x=y:=by induction q with
 | point i h=>exact ⟨Mist.point i,h,rfl⟩
 | midline _ _ i j =>
   obtain ⟨a,i,h⟩:=i; obtain ⟨b,j,t⟩:=j; exact ⟨a.midP b,And.intro i j,by change (1/2:ℂ) • (tide P a x+tide P b x)=_; rw [h,t]⟩
lemma advances (x:H){r ε:ℝ} (v:0<r)(t:0<ε):∃ D: Whisper Γ, aloof r D ∧ dist (tide P D x) (P.pi_c x) ≤ ε:=by
 obtain ⟨y,hy,h⟩:= Metric.mem_closure_iff.mp (P.haze_projection x r v) ε t; obtain ⟨D,v,hD⟩:=mist_of_hull P hy; exact ⟨D,v,(by rw [dist_comm,hD]; exact h.le)⟩
def brew : Whisper Γ:= D.via (fun i=> E.onFn (fun j=> i+j))
lemma brewed {r ε:ℝ}(p:aloof r D)(q:aloof ε E):aloof (r+ε) (brew D E):=by
 refine (D.hold_via ..).2 (D.promotes ?_ p); intro i h; refine (E.hold_via ..).2 (E.promotes ?_ q); intro j t; change |((i+j:↥Γ):ℝ)| < _; rw [AddSubgroup.coe_add]; exact (abs_add_le ..).trans_lt (add_lt_add h t)
lemma tide_comp (x:H): tide P (brew D E) x=tide P D (tide P E x):=by
 simp_rw [tide_mean]; rw [brew,D.mean_via]; refine D.mean_congr _ (D.solves _ fun i=>?_)
 rw [E.mean_onFn, ← E.mean_linear' _ (P.play i)]; exact E.mean_congr _ (E.solves _ fun j=>(P.paved H i j x).symm)
lemma tide_brews : tide P (brew D E)=tide P (brew E D):=by
 unfold tide brew; rw [D.mean_via,E.mean_via]; simp_rw [Mist.mean_onFn]
 change D.mean (fun i=>E.mean (fun j=> P.play (i+j)))= _; rw [D.mean_comm]; simp [Function.comp_def,add_comm] -- tune
lemma preserves_here (x:H)(h:x∈P.lives H){ε:ℝ}(e:0<ε): ∀ᶠ r:ℝ in 𝓝 0, ∀ D:Whisper Γ, aloof r D→ dist (tide P D x) x ≤ ε:=by
 obtain ⟨δ,d,H⟩:= P.living.mp h ε e
 filter_upwards [gt_mem_nhds d] with r hr D p; rw [tide_mean]; exact D.ceiling _ x ε (D.promotes (fun i h=>(H i (h.trans hr)).le) p)

section simultaneous
variable {I:Type*}{A:I→Hilbert}(K:∀i,Players Γ (A i))
abbrev Suite:= Σ i:I,(A i).space -- syntax
local notation "X"=> Σ i:I,(A i).space
local notation "σ" z:max=> tide (K z)
local notation "π" i:max=> (K i).pi_c
def answers (ε:ℝ) (D:Whisper Γ)(x : Σ i:I,(A i).space) : Prop:= dist ((σ x.1) D x.2) ((π x.1) x.2) ≤ ε
lemma dedication (s:Finset (Σ i:I,(A i).space)) (r ε:ℝ)(v:0<r)(e:0<ε): ∃ D: Whisper Γ, aloof r D ∧ ∀ x∈ s, answers K ε D x:=by
 induction s using Finset.cons_induction generalizing r ε with
 | empty=> exact ⟨Mist.point 0,(by change |((0:↥Γ):ℝ)| < r; simpa),by simp⟩
 | cons i S _ ih=>
   have he':∀ᶠ r':ℝ in 𝓝 0,∀ x ∈ S.cons i ‹_›, ∀ D: Whisper Γ, aloof r' D→ dist (tide (K x.1) D ((π x.1) x.2)) ((π x.1) x.2) ≤ ε/2:=by
     rw [Finset.eventually_all]; intro x _; exact preserves_here (K x.1) _ ((K x.1).repaired _) (by positivity)
   have ha:∀ᶠ r':ℝ in 𝓝[>]0, r'>0:=self_mem_nhdsWithin
   have he := (ha.and (show ∀ᶠ r':ℝ in 𝓝[>]0, r'<r/2 from mem_nhdsWithin_of_mem_nhds (gt_mem_nhds (show (0:ℝ)<r/2 by positivity)))).and (he'.filter_mono nhdsWithin_le_nhds)
   obtain ⟨r',⟨hh,u⟩,w⟩:= he.exists
   obtain ⟨D,d,h⟩:= ih r' (ε/2) hh (by positivity); obtain ⟨B,b,a⟩:= advances (K i.1) i.2 hh (show 0<ε/2 by positivity)
   have ze(D B: Whisper Γ)(x:X) (t: answers K (ε/2) B x)(p:aloof r' D)(q:x∈S.cons i ‹_›): answers K ε (brew D B) x:=by
     let A:= tide (K x.1) D; let Y:=tide (K x.1) B; let y:=x.2; let z:=(π x.1) y
     unfold answers; rw [tide_comp]; change dist (A (Y y)) z≤ ε
     exact (dist_triangle _ (A z) _).trans ((add_le_add ((tide_contract (K x.1) D (Y y) z).trans t) (w x q D p)).trans_eq (add_halves ε))
   refine ⟨brew B D,(brew B D).promotes (q:=fun i=>|(i:ℝ)| < r) (fun i t=> lt_trans t (show r'+r'<r by linarith)) (brewed B D b d),?_⟩
   intro x q; rcases Finset.mem_cons.mp q with z|z
   · unfold answers; rw [tide_brews]; exact ze D B x (z.symm ▸ a) d q
   exact ze B D x (h x z) b q
lemma worldP [Countable I][∀ i,TopologicalSpace.SeparableSpace (A i).space] :
    ∃ M:ℕ→Whisper Γ,(∀ ε>0, ∀ᶠ n in atTop, aloof ε (M n))∧∀ i x,Tendsto (fun n=> tide (K i) (M n) x) atTop (𝓝 ((π i) x)):=by
 -- approx on incidence
 let Z:= Σ i:I,ℕ; let k(z:Z): (A z.1).space := denseSeq _ z.2; let f:Z→X:=fun z=> ⟨z.1,k z⟩; let δ(n:ℕ):ℝ:=(1/2)^n; have vd(n):0<δ n:=by positivity
 have ht:Tendsto δ atTop (𝓝 0):=tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
 haveI: Encodable Z:= Encodable.ofCountable _; let S(n:ℕ):Finset Z:= (Finset.range n).biUnion (fun i=>(Encodable.decode i).toFinset)
 choose M hm h using fun n=> dedication K ((S n).image f) (δ n) (δ n) (vd n) (vd n)
 refine ⟨M,fun ε e=> (ht.eventually (gt_mem_nhds e)).mono fun n u=> (M n).promotes (fun i v=>lt_trans v u) (hm n),fun i x=>?_⟩
 refine Metric.tendsto_nhds.mpr fun ε e=>?_
 obtain ⟨y,p,v⟩:= Metric.mem_closure_iff.mp (denseRange_denseSeq (A i).space x) (ε/3) (by positivity)  -- name
 obtain ⟨r,rfl⟩:= p
 let a:Z:=⟨i,r⟩; let y:=(k a)
 filter_upwards [ht.eventually (gt_mem_nhds (show 0<ε/3 by positivity)),eventually_gt_atTop (Encodable.encode a)] with n hn p
 have q:a∈ S n:= Finset.mem_biUnion.mpr ⟨Encodable.encode a,Finset.mem_range.mpr p,(by rw [Encodable.encodek]; simp)⟩
 have w: dist (tide (K i) (M n) y) ((π i) y) < ε/3:= lt_of_le_of_lt (h n (f a) (Finset.mem_image_of_mem _ q)) hn
 let A_ := tide (K i) (M n); let Y:=π i; have hv: dist (Y x) (Y y)≤dist x y:=by simp only [dist_eq_norm,← map_sub]; apply Submodule.norm_starProjection_apply_le
 change dist (A_ x) (Y x)< ε
 change dist (A_ y) (Y y) < _ at w
 change dist x y < _ at v
 linarith [dist_triangle (A_ x) (A_ y) (Y x),dist_triangle_right (A_ y) (Y x) (Y y),(show dist (A_ x) (A_ y) ≤ dist x y from tide_contract (K i) _ _ _)]
end simultaneous
end YM.CF.Buffered.Afterglow.Tower.Aria
#print axioms YM.CF.Buffered.Afterglow.Tower.Aria.worldP
