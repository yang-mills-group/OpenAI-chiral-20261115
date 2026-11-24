import YM.SU5.Aria.Footpath
import YM.SU5.Aria.Screens
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 4500
set_option maxHeartbeats 220000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.VacuumSelection
open Function Filter NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock Analysis SlabMark MeshClock SatinVerification Vacancy Tapestry
open Germ Alliance
namespace Spine
variable (P: Spine) (j:Axis) (x:P.Spectrum0 j)
open Aria Set TopologicalSpace Metric
local notation "Λ"=> P.par
local notation "K"=> P.calibration
local notation "H"=> P.large
local notation "Y₀"=> P.run
local notation "Φ" => P.colorSpace j x
local notation "ω"=>P.colorZero j x
local notation "X₀"=> P.ColorHil j x
local notation "Χ"=> P.ManyF j x
local notation "Μ"=> timeMesh P.par
local notation "N"=> notch (timeMesh P.par)
local notation "Γ"=> P.VMark
local notation "κ"=> P.laysM
local notation "ψ"=> P.physicalEnergy j x
local notation "ν"=> P.seasons j x
local notation "E"=> (P.physicalEnergy j x).E
lemma sector_hot (t:ℝ≥0): (P.physicalEnergy j x).E t ω=ω:= by
 apply (P.gnsIn j x).injective
 change P.gnsIn j x (P.warming j x t ω)=P.gnsIn j x ω; rw [P.warmTransit,P.present0,P.at_full]
lemma heaven_hot (t:ℝ≥0): (P.seasons j x).E t (P.heaven j x)=P.heaven j x:= by
 apply (P.enter j x).injective; rw [P.soleHeat]; exact P.sector_hot j x t
namespace Apron
abbrev time_panel (v:Vantage)(D:P.Apron) : ℝ := v j - D.realWidth P j
abbrev time_edge (v:Vantage)(D:P.Apron):ℝ:= v j+D.realWidth P j
end Apron
variable {I:Type*} (A:I→P.Apron)
abbrev porchY (q:I→ Vantage)(i:I):ℝ := Apron.time_panel P j (q i) (A i)
abbrev resignY (q:I→ Vantage)(i:I):ℝ := Apron.time_edge P j (q i) (A i)
local notation "u✩" p:max=> P.porchY j A p
local notation "v✩" p:max=> P.resignY j A p
/-- demand pairwise slack (not touch allowed) on THIS axis -/
abbrev Turnstile (l:List I)(p:I→Vantage):Prop:= l.Pairwise (fun i k=> (v✩ p) i < (u✩ p) k)
abbrev commuteLoose (r:I→P.VMark)(i:I): (X₀).Op:= P.charter j x (r i) ((A i).engine P j x)
abbrev commuteTight (r:I→Vantage)(i:I):(Χ).Op:= P.tableau j x (r i) ((A i).engine P j x)
noncomputable def memorial (l:List I)(p:I→ Vantage):ℂ:= receive (ν) (P.heaven j x) (P.commuteTight j x A p) (u✩ p) (v✩ p) l
noncomputable def preview (l:List I)(p:I→ P.VMark):ℂ:= receive (ψ) ω (P.commuteLoose j x A p) (u✩ (κ ∘ p)) (v✩ (κ ∘ p)) l
local notation "u" p:max => (u✩ (κ ∘ p))
local notation "v" p:max => (v✩ (κ ∘ p))
variable (r:I → Cover) (n:ℕ)
local notation "q"=> P.vtile n ∘ r
lemma bell_sub (d e:ℤ): bell Μ n (d-e)=bell Μ n d-bell Μ n e:=by unfold bell; rw [Int.cast_sub,_root_.sub_mul]
lemma bell_move(j:Axis)(g:Cover):P.laysM (P.vtile n g) j=bell Μ n (g j):=rfl
local notation "a✩"=>P.firstLeg j n A r
local notation "b✩"=>P.lastLeg j n A r
lemma begins(i:I)(t:(A i).s≤n): bell Μ n (P.firstLeg j n A r i)= (u (P.vtile n ∘ r)) i:=by
 change bell Μ n (_-_)= _-(A i).realWidth P j; rw [P.bell_sub, Apron.zoom_bell P j (A i) n t]; rfl
lemma endsAt(i:I)(t:(A i).s≤n): bell Μ n (P.lastLeg j n A r i)= (v (P.vtile n ∘ r)) i:=by change bell Μ n (_+_)= _+(A i).realWidth P j; rw [bell_add,Apron.zoom_bell P j (A i) n t]; rfl
lemma transporting (l:List I)(b:ℤ)(t:P.onBoard j n A r l b)(g:∀ i∈ l,(A i).s ≤ n): P.eRide j x n A r l b=rector (ψ) (P.commuteLoose j x A q) (u q) (v q) l (bell Μ n b) ω:=by
 induction l generalizing b with
 | nil=>rfl
 | cons i L ih=>
   let d:= (a✩ i-b).toNat; obtain ⟨e,t⟩:=t; have he:(d:ℤ)=a✩ i-b:= Int.toNat_of_nonneg (sub_nonneg.mpr e); let B:= P.commuteLoose j x A q i; let s:=(u q) i; let s':=(v q) i
   have hz: (A i).s≤ n:= g i (List.Mem.head ..); change E (whenly Μ n d) (B (P.eRide j x n A r L (b✩ i)))= E (Real.toNNReal (s - bell Μ n b)) (B (rector _ _ _ _ L s' ω))
   rw [ih _ t (fun j y=> g j (List.Mem.tail _ y)), P.endsAt j A r n i hz]
   unfold s; rw [←P.begins j A r n i hz,← P.bell_sub,← he,natural_time,show (whenly Μ n d).val.toNNReal=whenly Μ n d from Real.toNNReal_coe]
   try rfl -- maybe no goals
lemma turn_board (l:List I)(b:ℤ)(s:P.Turnstile j A l (κ ∘ q))(p:∀ i L,l=i::L→ b≤a✩ i)(t:∀ i∈l,(A i).s≤n): P.onBoard j n A r l b:=by
 induction l generalizing b with
 | nil=>trivial
 | cons i L ih=>
   obtain ⟨e,s⟩:=List.pairwise_cons.mp s; refine ⟨p _ _ rfl,ih (b✩ i) s ?_ (fun j y=> t j (List.Mem.tail _ y))⟩; intro j' L₁ h; refine (bell_le Μ n _ _).1 ?_
   have hh:j'∈L:=by rw [h]; exact List.Mem.head ..; -- newline
   rw [P.endsAt j A r n i (t i (List.Mem.head ..)), P.begins j A r n j' (t j' (List.Mem.tail _ hh))]; exact (e j' hh).le
/-- intrinsic axis reading on chronological overlap, at grid. Important: not saying it is
 continuous. Uses transfer of `A i` same native mark, no invocation of products on overlapping O-supports. -/
lemma turn_purchase (l:List I)(s:P.Turnstile j A l (P.laysM ∘ (P.vtile n ∘ r)))(t:∀i∈l,(A i).s≤n): P.preview j x A l (P.vtile n ∘ r)=P.singleState j n x (P.fullScroll n A r l):=by
 have he:∃ b:ℤ,P.onBoard j n A r l b:=by cases l with
    | nil=>exact ⟨0,trivial⟩
    | cons i l=>exact ⟨a✩ i,P.turn_board j A r n _ _ s (fun i' L p=> (List.cons.inj p|>.1) ▸ le_refl _) t⟩ -- cast might fail
 obtain ⟨b,p⟩:=he; rw [← P.wagon j x n A r l b p t,P.transporting j x A r n l b p t]; exact (rector_view _ _ _ _ _ (P.sector_hot j x) _ l).symm
-- cert for approximating any geometry by finite rulers
variable (L:List I)
def onMark (y:I→ P.VMark) : Prop:= ∃ r:I → Cover,(∀ i∈L,(A i).s≤n)∧∀ i∈ L,P.vtile n (r i)= y i
lemma vwhere {g:Γ} (d:ℕ)(i:Axis): ∀ᶠ n:ℕ in atTop, ∃ k:ℤ, N n k=g i:=by
 obtain ⟨s,k,h⟩:=notch_exists Μ (g i); exact (eventually_ge_atTop s).mono fun i u'=> ⟨_, (notch_up Μ _ _ u' k).trans h⟩
lemma vmarks (y:I→ P.VMark) : ∀ᶠ n:ℕ in atTop, P.onMark A n L y:=by
 have hv:∀ i:I, ∀ᶠ n:ℕ in atTop, (A i).s ≤ n∧ ∃ r: Cover,P.vtile n r= y i:=by
    intro i; filter_upwards [eventually_ge_atTop (A i).s, Filter.eventually_all.mpr fun j:Axis=> P.vwhere («g»:=y i) 0 j] with n h t; choose k p using t; exact ⟨h,k,funext p⟩
 haveI:DecidableEq I:= Classical.typeDecidableEq I
 refine ((eventually_all_finset L.toFinset).mpr fun i z=>hv i).mono fun k hk=>?_ ; choose! f F using fun i (p:i∈L)=>(hk i ((List.mem_toFinset).mpr p)).2; exact ⟨f,fun i z=> (hk i ((List.mem_toFinset).mpr z)).1,F⟩
-- for existential consistency, replace offsets outside L
lemma turn_lists_fax (p s:I→Vantage)(h:∀ i∈ L,p i=s i)(u₀:P.Turnstile j A L p):P.Turnstile j A L s:=by induction L with
 | nil=>exact List.Pairwise.nil
 | cons i L ih=>
   obtain ⟨y,t⟩:= List.pairwise_cons.mp u₀; refine List.pairwise_cons.mpr ⟨fun x v₀=> ?_,ih (fun j u' => h j (List.Mem.tail _ u')) t⟩
   unfold porchY resignY; rw [← h x (List.Mem.tail _ v₀),←h i (List.Mem.head ..)]; exact y x v₀
section congru
variable {B:Hilbert}(S': OS.Semigroup B j)(Ω:B)
lemma rector_lists_fax (p s k w :I→ℝ)(Q T:I→B.Op)(h:∀ i∈ L,p i=s i ∧ k i=w i ∧ Q i=T i)(b:ℝ): rector S' Q p k L b=rector S' T s w L b:=by induction L generalizing b with
 | nil=> rfl
 | cons i L ih=>
    obtain ⟨e,f,g⟩:=h i (List.Mem.head ..); rw [rector_left,rector_left,e,f,g,ih (fun i y=> h i (List.Mem.tail _ y))]
lemma receive_list_fax (p s k w:I→ℝ)(Q T:I→B.Op)(h:∀ i∈ L,p i=s i∧k i=w i∧ Q i=T i): receive S' Ω Q p k L=receive S' Ω T s w L:=by
 unfold receive; have hu: before p L=before s L:=by cases L with | nil=> rfl | cons i L=>exact (h i (List.Mem.head ..)).1
 rw [hu,rector_lists_fax j L _ _ _ _ _ _ _ h]
end congru
lemma preview_lists_fax (p s:I→Γ)(h:∀ i∈ L,p i=s i): P.preview j x A L p=P.preview j x A L s:=by
 apply receive_list_fax j L (ψ) ω _ _ _ _ _ _; intro i t
 unfold porchY resignY Function.comp commuteLoose; rw [h i t]; exact ⟨rfl,rfl,rfl⟩
lemma match_forecast (i₀ g:Axis)(l:List I)(t:L.Perm l)(r:I→Γ)(p:P.Turnstile i₀ A L (P.laysM ∘ r))(c:P.Turnstile g A l (P.laysM ∘ r)): P.preview i₀ (P.advocate j x i₀) A L r=P.preview g (P.advocate j x g) A l r:=by
 obtain ⟨n,f,h,v'⟩: ∃ n:ℕ,P.onMark A n L r:= (P.vmarks A L r).exists
 have u':∀ i∈ l,P.vtile n (f i)= r i := fun i y=> v' i (t.mem_iff.mpr y)
 let F:= P.vtile n ∘ f; have hx:= P.turn_lists_fax i₀ A L (κ ∘ r) (κ ∘ F) (fun i t=> congrArg _ (v' i t).symm) p; have ht: P.Turnstile g A l (κ ∘ F):= P.turn_lists_fax g A l (κ ∘ r) _ (fun i h=> congrArg _ (u' i h).symm) c
 rw [← P.preview_lists_fax i₀ (P.advocate j x i₀) A L F r v',← P.preview_lists_fax g (P.advocate j x g) A l F r u',P.turn_purchase i₀ (P.advocate j x i₀) A f n L hx h,P.turn_purchase g (P.advocate j x g) A f n l ht (fun i y=> h i (t.mem_iff.mpr y)),P.fullScroll_perm n A f t]
 exact (P.single_agrees j i₀ x n (P.fullScroll n A f l)).trans (P.single_agrees j g x n _).symm
end Spine
end YM.CF.Buffered.Afterglow.Tower.VacuumSelection
