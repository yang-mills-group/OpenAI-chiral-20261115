import YM.SU5.FiniteGaugeData.Concord.Delivery
/-! # Consequences for the full nonseparable observable algebra on our FiniteGaugeData election -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option maxHeartbeats 420000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical TensorProduct
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock Heat
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ:Preparation}{l:ℕ} (Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Playhouse Λ l}
variable {i k:ℕ→ℕ} (W:Traced Y H i k F E P)
variable (s n d:ℕ)
local notation "K"=> tent Y H
local notation "X" => Hallspace (tent Y H)
local notation "Ω" => ConeFilter Y i k
local notation "ν"=> side Y n s
local notation "ρ" => realizeStage Y H n d s W
local notation "E'"=> starGem Y H W s

variable (x y:Hallspace (tent Y H))

-- linearity and coherence of the local mixed limit in each large period.
-- Use congruence eventually for every x with proper through-level suite.

lemma reader_zero : reader Y H n d s W 0=0:=by
  unfold reader; rw [map_zero]; change compass _ _ _ _ 0=_; nth_rw 1 [←zero_smul ℂ (0:Mark ν)]; rw [voice_smul,zero_mul] -- rewrite issue
lemma reader_add (t: PairIdx Y s n d): reader Y H n d s W (x+y)=reader Y H n d s W x+reader Y H n d s W y:= by unfold reader; rw [map_add]; exact voice_add Y t.1 t.2.le (show AtSupport false univ ((ρ) x).val from ((ρ) x).property).env (show AtSupport false univ ((ρ) y).val from ((ρ) y).property).env
lemma reader_scale (a:ℂ): reader Y H n d s W (a•x)= a*reader Y H n d s W x:=by unfold reader; rw [map_smul]; exact voice_smul ..

def attraction (g:ℕ→ℂ) :Prop:=
    (∀ᶠ n:ℕ in atTop,Tendsto (fun d=> reader Y H n (k d) s W x) atTop (𝓝 (g n))) ∧
    Tendsto (g ∘ i) atTop (𝓝 (starGem Y H W s x)) ∧
    Tendsto (fun j:ℕ×ℕ=> reader Y H (i j.1) (k j.2) s W x) (ConeFilter Y i k) (𝓝 (starGem Y H W s x))

lemma attraction_zero : attraction Y H W s 0 0:=by
 unfold attraction starGem; rw [map_zero,map_zero]; simp_rw [reader_zero]; exact ⟨Eventually.of_forall fun _=> tendsto_const_nhds,tendsto_const_nhds,tendsto_const_nhds⟩
lemma attraction_add {f g:ℕ→ℂ}(a:attraction Y H W s x f)(b:attraction Y H W s y g) : attraction Y H W s (x+y) (f+g):=by
 have he: E' (x+y)=E' x+E' y:=by simp only [starGem,map_add]
 refine ⟨(a.1.and b.1).mono (fun n h=> (h.1.add h.2).congr' ((row_use W.own.pick s n).mono fun _ t=> ?_)), he.symm ▸ a.2.1.add b.2.1,?_⟩
 · exact (reader_add Y H W s _ _ _ _ t).symm
 let l:= timely_visit W.own.pick s
 rw [he]; exact (a.2.2.add b.2.2).congr' (l.mono (fun _ t=> (reader_add Y H W s _ _ _ _ t).symm))
lemma attraction_scale (a:ℂ){f:ℕ→ℂ} (t:attraction Y H W s x f): attraction Y H W s (a•x) (a•f):=by
 have he : starGem Y H W s (a•x)=a • starGem Y H W s x:=by simp only [starGem,map_smul]
 refine ⟨t.1.mono (fun n h=> (h.const_mul a).congr (fun _=>(reader_scale ..).symm)),by rw [he]; exact t.2.1.const_mul a,?_⟩
 rw [he]; exact (t.2.2.const_mul a).congr (fun _=>(reader_scale ..).symm)
lemma current_reading (t:x∈Style.atLeast (A:=↥(junior K)) s): ∃ g:ℕ→ℂ,attraction Y H W s x g:=by
 refine Style.display (P:=fun x=>∃ g:ℕ→ℂ,attraction Y H W s x g) ?_ ⟨_,attraction_zero ..⟩ (fun _ _ _ _ ⟨_,a⟩ ⟨_,b⟩=>⟨_,attraction_add Y H W s _ _ a b⟩) (fun a _ _ ⟨_,b⟩=>⟨_,attraction_scale Y H W s _ a b⟩) (show x∈Style.pressed _ from t)
 intro p a; let S:=fun i=>(supported K (p i)).choose; let f(i:ℕ):= polish K (S i) (p i) (supported K (p i)).choose_spec
 exact ⟨_, Meet.registers Y H W S s f p (fun i _=> (polish_eq ..).symm) a.2⟩

include W
lemma different_rows {f₀ f₁:ℕ→ℂ}{t₀ t₁:ℕ}
    (p:x∈Style.atLeast (A:=↥(junior K)) t₀)(r:x∈Style.atLeast (A:=↥(junior K)) t₁)(h:attraction Y H W t₀ x f₀)(k':attraction Y H W t₁ x f₁): f₀ =ᶠ[atTop] f₁:=by
 let t:=max t₀ t₁
 filter_upwards [h.1,k'.1] with n v q; apply tendsto_nhds_unique_of_eventuallyEq v q;
 filter_upwards [row_use W.own.pick t n] with d g
 exact (memorable _ _ _ _ _ W (t:=t) (le_max_left ..) p g.1 g.2.le).trans (memorable _ _ _ _ _ W (t:=t) (le_max_right ..) r g.1 g.2.le).symm

-- corresponding consumer on whole physical or even building, no loss of determination
lemma building_quote (x:building K)(t:x.val∈Style.atLeast (A:=↥(junior K)) s):
    ∃ g:ℕ→ℂ,(∀ᶠ n:ℕ in atTop,Tendsto (fun d=> reader Y H n (k d) s W x.val) atTop (𝓝 (g n))) ∧
    Tendsto (g ∘ i) atTop (𝓝 (portfolio Y H W x)) ∧ Tendsto (fun j:ℕ×ℕ=> reader Y H (i j.1) (k j.2) s W x.val) (ConeFilter Y i k) (𝓝 (portfolio Y H W x)):=by
 rw [portfolio_hall Y H W t,←intake_eq Y H s W.own]; exact current_reading Y H W s x.val t

-- actual singlet interpretation where provided at these levels
omit W
private def guild (s : Side) : Subalgebra ℂ (grammar s) where
 carrier := {f|covariant f.val}
 add_mem':= fun {x y} t v g a=> by
   change x.val _+y.val _=twist _ (x.val a+y.val a); rw [map_add,(show covariant x.val from t) g a,(show covariant y.val from v) g a]
 mul_mem':= fun {x y} t v g a=> by
   change x.val _*y.val _=twist _ (x.val a*y.val a); rw [map_mul,(show covariant x.val from t) g a,(show covariant y.val from v) g a]
 algebraMap_mem' c:=by rw [Algebra.algebraMap_eq_smul_one]; intro g a; change c • (1:FC (Single s)) =twist _ (c • 1); rw [twist_scalar,map_one]
lemma stage_guild (f:ℕ→junior K)(t:∀ i ≤ s, f i∈singlets K)(p:(Y.voyage n).kick ≤ d)(v:s≤ Y.uv d):
    covariant (stagewrap Y H n d s f).val:=by
 induction s with
 | zero=> exact gauge_observed Y H 0 n (f 0) (t 0 le_rfl)
 | succ s ih=>
   rw [stage_next]; apply (guild (side Y n (s+1))).mul_mem _ (show covariant (sceneL Y H n (s+1) (f (s+1))).val from gauge_observed Y H (s+1) n _ (t (s+1) le_rfl)) -- result
   let F:=stagewrap Y H n d s f; let z:PairIdx Y s n d:= ⟨p,v⟩; change covariant (scenic Y n d s F).val; rw [ticket_v Y n d s z]; exact haul_gauge Y s n d z F.val F.property (ih (fun i u=>t i (by omega)) (Nat.le_of_lt v)) -- order relative d assumptions

include W
lemma currently_gauge (t:x∈limited (fun _=>singlets K) s)(p:(Y.voyage n).kick ≤ d)(v:s≤Y.uv d):
    covariant (realizeStage Y H n d s W x).val:=by
 refine Style.display (P:=fun x=> ρ x∈ guild (side Y n s)) ?_ ?_ ?_ ?_ (show x∈Style.pressed _ from t)
 · intro f u; have he:= (pepper_rule ..).1 u; rw [stage_e Y H n d s W f he.2]; exact stage_guild Y H s n d f he.1 p v -- arg
 · rw [map_zero]; exact Subalgebra.zero_mem _
 · intro x y _ _ a b; rw [map_add]; exact Subalgebra.add_mem _ a b
 intro a x _ b; rw [map_smul]; exact Subalgebra.smul_mem _ b a

lemma issue_gauge (t:x∈limited (fun _=>singlets K) s): issue Y H W s x∈singlets K:=by
 have he(m:ℕ)(f:ℕ→junior K)(p:∀ i ≤ m,f i∈singlets K) : (Style.prefixTube _ (fun _=> LinearMap.id) (fun s=> courseAdvance Y H s W) m).soc f∈singlets K:=by
   induction m with | zero=> exact p 0 le_rfl | succ i ih=> rw [Style.vystep]; exact Subalgebra.mul_mem _ (curtain Y H i W _ (ih fun j t=> p j (by omega))) (p _ le_rfl)
 refine Style.display (P:=fun x=> issue Y H W s x∈singlets K) ?_ ?_ ?_ ?_ (show x∈Style.pressed _ from t)
 · intro f v; have h:= (pepper_rule ..).1 v; rw [solo_issue Y H W f h.2]; exact he s f h.1
 · rw [map_zero]; exact Subalgebra.zero_mem _
 · intro x y _ _ a b; rw [map_add]; exact Subalgebra.add_mem _ a b
 intro a x _ b; rw [map_smul]; exact Subalgebra.smul_mem _ b a

-- For an actual `physical` element, choose meeting level qualifying ALL requirements (provided). Then transport beyond.
omit W
lemma through {xu:Hallspace (tent Y H)}(t:xu∈physical (tent Y H)):
    ∃ s:ℕ,∀ t,s≤t → xu ∈ limited (fun _=>singlets (tent Y H)) t := by
  obtain ⟨n,v⟩:= Style.by_stages _ _ (show xu∈throughout (fun _=>singlets (tent Y H)) from t); exact ⟨n,fun _ d=> Style.to_pepper _ d v⟩
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.building_quote
#print axioms YM.CF.Buffered.Concord.different_rows
#print axioms YM.CF.Buffered.Concord.currently_gauge
