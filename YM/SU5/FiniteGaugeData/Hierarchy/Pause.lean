import YM.SU5.FiniteGaugeData.Hierarchy.Metro
/-! # No dependence on choice of support or observing horizon for these recipes
in all the cited readouts on paid entries. `inPrice` uses a support choice,
show equality on the common room (sufficiently late periods). -/
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
local notation "W₀" => GridStep Λ l S
variable {u v:ℕ→ℕ}{I:ℕ→Family (tent Y h)→ℕ→ℂ}{E:ℕ→Family (tent Y h)→ℂ}
variable {P:Call Λ l}{J:Wicket Λ l}
variable (K:Universal Y h u v I E)(R:Rolled Y h u v J P)
open Charm
namespace Playlist
namespace Show
open Girt
set_option maxHeartbeats 370000
local notation "U" => W (tent Y h)
local notation "M" => Motif (tent Y h)
local notation "H₁"=> Theater (tent Y h)

variable (Z:ℕ→ Finset Cover)
local notation "Hᵣ" i:max => folio Λ l Z i
local notation "Wᵣ" i:max => GridStep Λ l (folio Λ l Z i)
local notation "Dₛ" i:max => salary Y h (folio Λ l Z i) i
section
private lemma real_next (x:Theater (tent Y h))(g:Works Y Z i k s)(u:Contract Y h Z x)(v:Arrive Y h x s):
    ingress Y s i k (actual Y h s i k x)=actual Y h (s+1) i k x:=by
 let τ:=g s le_rfl; let A:= x.coeff.support; let n:= side Y i s; let f (m:M):=story Y h i k m s; let T:= region (Hᵣ s) n
 let F(m:M):= x.coeff m • f m; have h'(m:Motif Kₜ)(h0:m∈A): AtSupport false (region (Hᵣ s) n) (F m):= ((native_account Y h s i k Z m ((active_iff ..).mp u _ h0) g).1.smulM _)
 have ht(m:M)(t:m∈A): story Y h i k m (s+1)=ingress Y s i k (f m):= by rw [story,v m t (s+1) (by omega),identityW,sold_one,mul_one]
 classical
 let d(m:M):=x.coeff m • story Y h i k m (s+1); let Q:= ingress Y s i k
 suffices e: ∀ Z:Finset (Motif Kₜ), Z⊆ A→ AtSupport false T (∑ i∈Z,F i) ∧ Q (∑ i∈Z,F i)=∑ i∈Z,d i from (e A (Subset.refl _)).2
 intro Z
 induction Z using Finset.induction_on with
 | empty=> intro p; rw [sum_empty,sum_empty]; refine ⟨AtSupport.zeroM,?_⟩; exact (by simpa only [smul_zero,zero_smul] using ingress_scale Y s i k 0 0)
 | @insert i' Z v ih =>
   intro v'
   let u:= v' (mem_insert_self ..); obtain ⟨p,e⟩:=ih fun _ hℓ=>v' (mem_insert_of_mem hℓ)
   rw [sum_insert v,sum_insert v]; let r:=h' i' u; refine ⟨r.addM p,?_⟩
   unfold Q at e; rw [show Q (F i'+_) =_ from ingress_add Y s i k τ.calendar τ.age r p,e]
   unfold d; rw [ht i' u]; exact congrArg (·+_) (ingress_scale Y s i k _ _)

lemma stability (x:Theater (tent Y h))(t:ℕ)(p: s ≤ t)(u:Contract Y h Z x)(v: Arrive Y h x s)(a:Works Y Z i k t):
    readout Y h s i k x= readout Y h t i k x:= by
  induction t,p using Nat.le_induction with
  | base => rfl
  | succ t p ih=>
    let T:Works Y Z i k t:= fun j q=>a j (by omega); let v':= (T t le_rfl); let r:= major Y h t Z x u (tour Y h i k) -- give t
    rw [ih T]
    change Journey.compass Y i k t _= _
    have he: (sold Y h t i) (composeQ Kₜ (Hᵣ t) r)= actual Y h t i k x:= actual_eq Y h t i k Z T x u
    rw [← he,← sold_sharp,refresh Y h (Hᵣ t) t i k v'.calendar v'.age _ (compose_t ..),he,real_next Y h t i k Z x T u ?_]
    exact fun m h=> ends_mono _ _ _ _ m (v m h) p

include h
lemma attend : ∀ᶠ i:ℕ in atTop, Simulated Y Z i s:= by
  filter_upwards [(eventually_all (ι:=Fin (s+1))).mpr (fun i=>solvent_often Y h (folio Λ l Z i) i)] with i t j p; exact t ⟨j,p.trans_lt (Nat.lt_succ_self _)⟩
include K
lemma relate (p:Simulated Y Z i s) : ∀ᶠ j:ℕ in atTop, Works Y Z i (v j) s:= by
  filter_upwards [(eventually_all (ι:=Fin (s+1))).mpr (fun k=> often_offer_inner Y h _ (k.val) i K (p k (by have h:=k.isLt; omega)))] with i t j p; exact t ⟨j,p.trans_lt (Nat.lt_succ_self _)⟩

include R
lemma aligns (x:Theater (tent Y h))(Z':ℕ→ Finset Cover)(t:ℕ)(p: s ≤ t) (a:Contract Y h Z x)(b:Contract Y h Z' x)(h': Arrive Y h x s): ∀ᶠ i:ℕ in atTop,inPrice Y h s i (J:=J) K Z x a=inPrice Y h t i (J:=J) K Z' x b:=by
  filter_upwards [(lifts Y h s K R Z x a h').1,(lifts Y h t K R Z' x b (fun m t=> ends_mono Y h _ _ _ (h' m t) p)).1,attend Y h t Z] with i A B c
  exact tendsto_nhds_unique_of_eventuallyEq A B ((relate Y h t i K Z c).mono fun k g=> stability Y h s i _ Z x _ p a h' g)
end
-- also the one-city identity is gauge singlet under the auxiliary tag action, not using a noninteracting prior here
lemma salable (x:H₁)(g:Works Y Z i k s)(a:Contract Y h Z x) (v:Orbit (side Y i s))(t:Seat (side Y i s)→SU.E) :
    let n:= side Y i s; let l':=(Y.voyage i).CapeT s; let z:= Tᵣ i k s
    let f:=fun v:Orbit n=>letterRead (actual Y h s i k x (drawn l' v)) (denZ z Λ.U l' v)
    f (gird t v)= f v:=by
  intro n T N F; unfold F; rw [Y.color i k s (covers Y s i k Z g).2]; let P:= quantU (tradew (side Y i s) t); let M':= actual Y h s i k x; let A:= M' (drawn T v); let X:= denZ N Λ.U T v
  rw [show drawn T (gird t v)= simultaneous t (drawn T v) from Prod.ext rfl (((Y.voyage i).ownership s).paid.rev ..), (actual_inside Y h s i k Z g x a).2 t (drawn T v)]
  change inner ℂ (Dial.mateK n) (acts (twist P A) (acts P.val X)) = _; rw [←Fock.swivel]; have he:=act_unit_inner P (Dial.mateK n) (acts A X); rw [show acts P.val (Dial.mateK n)=_ from Girt.mastC t] at he; exact he
#print axioms salable
end Show
end Playlist
end YM.CF.Buffered.Afterglow.Hierarchy
