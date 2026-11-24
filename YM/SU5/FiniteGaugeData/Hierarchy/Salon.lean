import YM.SU5.FiniteGaugeData.Hierarchy.Banquet
import YM.SU5.FiniteGaugeData.Marked.Variation.Performance
import YM.SU5.FiniteGaugeData.Hierarchy.Rich

/-! # Actual RG one-step on catalogs -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Hierarchy
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange Common Fock Pastry Satin
open Reed (Fine)
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Fiber Vale VolumeCape FullBill
set_option quotPrecheck false
variable {Λ:Preparation}{l:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus l))(h:Real.exp 1≤ Λ.x)
local notation "Kₜ"=> tent Y h
local notation "N₁" i:max s:max=> side Y i s
local notation "Wₐ" i:max s:max => (Y.voyage i).CapeT s
local notation "D₀"=> aliasLaw Λ
local notation "D₁"=> distanceLaw l
local notation "L₁"=> Λ.R.L
local notation "C₀"=> (VolumeCape.Dream.plot l).C
local notation "Xᵣ" i:max k:max=> (Y.voyage i).X (Y.uv k)
local notation "Tᵣ" i:max k:max s:max=> ((Y.voyage i).X (Y.uv k)).gram s
variable (S T: Finset Cover)(s i k:ℕ)

-- size at that observing level only
section ticket

def ship {n m:Side}(p:n=m) : Mark n ≃ₗ[ℂ] Mark m:= by subst m; exact LinearEquiv.refl ..
lemma ship_eq {n m:Side}(p:n=m)(f:Mark n) : ship p f=p▸ f:=by subst m; rfl
def sold : Family (tent Y h) →ₗ[ℂ] Mark (side Y i s) := (ship (terrain Y h (Y.ir i) s)).toLinearMap.comp (LinearMap.proj (φ:=fun m=>Mark ((tent Y h).c m)) (momentm Y i s))
local notation "P"=>sold Y h s i
lemma sold_v (f:Family Kₜ): sold Y h s i f=send Y h i s (f (momentm Y i s)):= ship_eq _ _
lemma sold_one : sold Y h s i 1=1:=by rw [sold_v]; exact (transformed Y h s i 0 0 0 0 0 0 (Classical.arbitrary _)).2.2.2.1
lemma sold_mult (f g:Family Kₜ): sold Y h s i (f*g)= sold Y h s i f * sold Y h s i g:=by
  simp_rw [sold_v]; exact (transformed Y h s i f g 0 0 0 0 (Classical.arbitrary _)).2.2.1
lemma sold_kiosk (f:PairsC→ℂ)(u:Chorus) : sold Y h s i (note Kₜ f u)=Satin.knot (side Y i s) u f := by
  rw [sold_v,kiosk]; exact castK (terrain Y h (Y.ir i) s) f u
where castK {n m:Side}(p:n=m)(f u) : (show Mark m from p ▸ Satin.knot n u f)= Satin.knot m u f:=by subst m; rfl
lemma sold_affair {b:Bool} {f:Family (tent Y h)} (p:InTest (tent Y h) true S b f): AtSupport b (region S (side Y i s)) (sold Y h s i f):=by
  rw [sold_v]; exact castK (terrain Y h (Y.ir i) s) _ (p.support _)
where castK {n m:Side}(e:n=m) (g: Mark n) (p:AtSupport b (region S n) g): AtSupport b (region S m) (e▸g):=by subst m; exact p
lemma sold_sharp (f:Family Kₜ): Journey.sharp Y h s i k f=Journey.compass Y i k s (sold Y h s i f):=by rw [sold_v]; rfl

lemma sold_q (x:Catalog S) (p:Hosp S (side Y i s)): takeScore S p (sold Y h s i (composeQ Kₜ S x))= source S x:=by
  rw [sold_v]; exact castK (terrain Y h (Y.ir i) s) p _ _ fun t=>take_source S Kₜ t x
where castK {n m:Side}(e:n=m)(p:Hosp S m)(g:Mark n)(x:Score S)(u:∀ p:Hosp S n,takeScore S p g=x) : takeScore S p (e▸g)=x:=by subst m; exact u p
lemma sold_q_bound (x:Catalog S) (v:Fields (side Y i s)) : ‖sold Y h s i (composeQ Kₜ S x) v‖ ≤ duration S * ‖x‖ := by
  rw [sold_v]; exact castK (terrain Y h (Y.ir i) s) _ (compose_price S Kₜ x _) _
where castK {n m:Side}(p:n=m){C:ℝ}(g:Mark n)(q:∀ v,‖g v‖≤ C) : ∀ v, ‖(show Mark m from p▸g) v‖ ≤ C:= by subst_vars; exact q
lemma sold_catalog_inj (p:Hosp S (side Y i s)) : Injective (fun f:Catalog S=> sold Y h s i (composeQ Kₜ S f)):=by
  intro f g e; have ht:source S f=source S g:=(sold_q Y h S s i f p).symm.trans ((congrArg (takeScore S p) e).trans (sold_q Y h S s i g p)); exact funext fun i=>stock_eq S (congrFun ht i)
lemma sold_surj (u: Roomy S (side Y i s)) (f:Mark (side Y i s)) (p: AtSupport false (region S (side Y i s)) f):
    ∃ x:Catalog S, sold Y h s i (composeQ Kₜ S x)=f:=by
  let m:=momentm Y i s; let v(x:Catalog S):= composeQ Kₜ S x m; let H:= terrain Y h (Y.ir i) s
  exact castK H u f p (fun x=>v x) (fun h f p=>into_catalog S Kₜ h p)
where castK {n m:Side}(p:n=m)(h:Roomy S m)(f:Mark m)(v:AtSupport false (region S m) f)(w: Catalog S→ Mark n)(a:Roomy S n→∀ f,AtSupport false (region S n) f→∃ x,w x=f):∃ x,ship p (w x)=f:=by subst m; exact a h f v
end ticket

/-- Support enlargement in gauge COVER units. Fixed S,s. -/
abbrev GridStep (Λ:Preparation)(l:ℕ) (S:Finset Cover) := liner (S.image (fun a=> Λ.R.L.val • a)) (Λ.R.L.val*gross (aliasLaw Λ) (distanceLaw l) Λ.R.J)
local notation "T₀"=> plaza (Λ:=Λ) S
local notation "W"=> GridStep Λ l S

def ingress :Mark (side Y i s) → Mark (side Y i (s+1)):= nextMark (j:=Λ.K.j) (ho:=Λ.R.odd_side) ((Xᵣ i k).gram) (Y.voyage i).CapeT Chi.canonical Λ.J.d ((Xᵣ i k).wave) (steps Λ.V (Y.ir i) Λ.block (Y.uv k)) s

local notation "Q" => ingress Y s i k
abbrev sized (s i:ℕ) : (side Y i (s+1)).val=(side Y i s).val*Λ.R.L.val := (apt (Y.ir i) Λ.block Λ.R.L s).exact_size
lemma pin_l : steps Λ.V (Y.ir i) Λ.block (Y.uv k) s = pegged Λ.R Λ.K.bind (sized Y s) i:= step_eq _ _ (Y.pilot_steps s i k).1 (Y.pilot_steps s i k).2.1
where step_eq {n m : Side}(X Y: StepData n m)(a:X.patch=Y.patch)(b:X.kernel=Y.kernel):X=Y:=by cases X; cases Y; congr

abbrev rayCost (s i k:ℕ):= ((Xᵣ i k).wave s).val
section

-- gate for actual classic and matched Step. Smaller than Ferry.
variable (a:(Y.voyage i).kick≤ k)(u:s<Y.uv k)
include a u
lemma crease : 0<Λ.J.d ∧ 2*Λ.J.d<firstRadius SU.group:=((fullness Y i k a).cap_grant.grant s u).some.legal
omit a u in
lemma reel (f:Mark (side Y i s)): ingress Y s i k f= pushMark (bead _ Λ.R.L _ (sized Y s) i) (pegged Λ.R Λ.K.bind (sized Y s) i) Λ.K.j (rayCost Y s i k) (Tᵣ i k (s+1)).J.M Λ.R.odd_side Chi.canonical Λ.J.d (Y.beta i k s) (Wₐ i s) f:=by
  unfold ingress nextMark; rw [pin_l]; rfl
lemma ingress_test {R:Support (More (side Y i s))}{f:Mark (side Y i s)}{b:Bool} (p:AtSupport b R f): AtSupport b (padded (apt (Y.ir i) Λ.block Λ.R.L s) R (Λ.R.L.val * gross (aliasLaw Λ) (distanceLaw l) Λ.R.J)) (ingress Y s i k f):=by
  let P:= (fullness Y i k a).cap_grant; let K:= Λ.K; let g:=apt (Y.ir i) Λ.block L₁ s; let t:=steps Λ.V (Y.ir i) Λ.block (Y.uv k) s; let W':= Tᵣ i k (s+1); let v:= crease Y s i k a u; have hv:= surround g t K.j (rayCost Y s i k) W'.J.M Λ.R.odd_side Chi.canonical Λ.J.d W'.beta (Wₐ i s) (show LaurentRadius _ _ _ from Journey.legal Λ) ((Y.voyage i).ownership s).paid.bill (P.branch s u) v.1 v.2 _ p (Journey.tissue Y i s) (P.aligned s u)
  have he: t.patch.J=Λ.R.J:= P.radius s u; rw [he] at hv; exact hv
lemma ingress_grid {f:Mark (side Y i s)}{b:Bool}(p:AtSupport b (region S (side Y i s)) f) : AtSupport b (region (GridStep Λ l S) (side Y i (s+1))) (ingress Y s i k f):= (ingress_test Y s i k a u p).mono (Satin.next_contains S _ _ _)

section
omit a u
private lemma sum_nat {N P:Side}(G:Ratio N P)(A:StepData (More N) (More P))(B:A.patch.Branches A.kernel SU.group) (j w:ℕ)(r:LaurentRadius j G.count w) (M:Male)(Qv:Op SU.Slot)(ho: Odd G.count.val)(q:Chi)(y β:ℝ)(K:Loom N)(m:Measurable K)(p:0<y)(e:2*y<firstRadius SU.group)(f g:Mark N)(h:Envelope f)(t:Envelope g)(u:Envelope (f+g)):
    let k:= pushMark G A j Qv M ho q y β K
    k (f+g)=k f + k g:=by
  intro k; funext W' ; let F := fun (f:Mark N) (x:Orbit N)=> A.density β W'.1 x.1 • gathered G j Qv M ho q y f W' (drawn K x)
  have he(f:Mark N)(h:Envelope f): k f W' = (∫ x,F f x∂city N):= outright G A j Qv M ho q y β K r m B p e _ h _
  have hv(f:Mark N)(h:Envelope f):Integrable (F f) (city N):= Env.integrableX (Env.scale (Env.along (slice_env A β B W'.1) measurable_fst) (Env.along (g:=fun x:Orbit N=>(W',drawn K x)) (env_gathered G j Qv M ho q y r p e f h) (measurable_const.prodMk (drawn_m K m)))) _
  rw [Pi.add_apply,he f h,he g t,he _ u,← integral_add (hv f h) (hv g t)]; exact integral_congr_ae (Eventually.of_forall fun i=>by unfold F gathered before avgF; simp only [Pi.add_apply,map_add,sum_add_distrib,smul_add] )
-- linear even where some free integrals weren't hoisted
private lemma push_scalar {N P:Side}(G:Ratio N P)(A:StepData (More N) (More P))(j:ℕ)(Q₁:Op SU.Slot)(M:Male)(ho:Odd G.count.val)(q:Chi)(d β:ℝ)(l:Loom N)(f:Mark N)(a:ℂ):
    let k:=pushMark G A j Q₁ M ho q d β l
    k (a • f)= a • k f:=by
  intro k; funext v; unfold k pushMark linkLaw Advance.assembled gathered before avgF; simp_rw [Pi.smul_apply,map_smul,← Finset.smul_sum,smul_comm _ a, integral_smul]
  simp_rw [smul_comm (M:=ℝ) _ a, integral_smul]
end
lemma ingress_add {R:Support (More (side Y i s))}{f g:Mark (side Y i s)}{b:Bool} (p:AtSupport b R f)(q:AtSupport b R g): ingress Y s i k (f+g)=ingress Y s i k f + ingress Y s i k g:=
  sum_nat (apt (Y.ir i) Λ.block Λ.R.L s) _ ((fullness Y i k a).cap_grant.branch s u) Λ.K.j (aliasLaw Λ) (Journey.legal Λ) _ _ Λ.R.odd_side Chi.canonical _ _ _ ((Y.voyage i).ownership s).paid.bill (crease Y s i k a u).1 (crease Y s i k a u).2 _ _ p.env q.env (p.addM q).env
omit a u in
lemma ingress_scale (f:Mark (side Y i s))(z:ℂ): ingress Y s i k (z • f)=z • ingress Y s i k f:= push_scalar (apt (Y.ir i) Λ.block Λ.R.L s) _ Λ.K.j _ _ Λ.R.odd_side Chi.canonical Λ.J.d _ _ f z

lemma refresh (f: Family Kₜ) (p:InTest Kₜ true S false f):
    sharp Y h s i k f= Journey.compass Y i k (s+1) (ingress Y s i k (sold Y h s i f)):=by
  rw [sold_sharp]; unfold Journey.compass; rw [single_num Λ.U (Xᵣ i k).gram (Y.voyage i).CapeT Chi.canonical Λ.J.d (Y.uv k) (Xᵣ i k).wave (steps Λ.V (Y.ir i) Λ.block (Y.uv k)) (Journey.legal _) (fullness Y i k a).cap_grant ((sold_affair Y h S s i p).mono (subset_univ _)) u, (Xᵣ i k).balance s u.le,← (Xᵣ i k).balance (s+1) u]
  rfl
end
end YM.CF.Buffered.Afterglow.Hierarchy
#print axioms YM.CF.Buffered.Afterglow.Hierarchy.refresh
