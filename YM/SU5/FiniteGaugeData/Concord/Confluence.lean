import YM.SU5.FiniteGaugeData.Concord.Aligned
/-!
# The sheaf of estimates glued across supports

Here is one calculus of estimate on a moving family of marks (not touching rates here, use
later where needed for products). *Fixed* support and *fixed* observing level, n→∞ & cutoff
in the ConeFilter, and measure and prices exactly the surveyed ones. `Sited` means norm
convergence in SOME fixed Box, with equality to actual native marks eventually there;
hence eventual continuity under this motion on all the actual estimates. Use on even chiral
marks. No need to attach this also to early periods outside that support's budget.
-/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option maxHeartbeats 480000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Concord
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker
  Topology ComplexOrder Classical
open Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent
  Next.Free Bloch Drapes Spire Lifted Skye Precision Tree Push.SectorMeasure Next.SectorChange Fock
open Afterglow Afterglow.Common Afterglow.Sound Afterglow.Satin
attribute [local instance] opCStarAlgebra
open Py Py.Rate LocalLimit Preparation Journey Vale
variable {Λ:Preparation}{l:ℕ}{Y:Course Λ (VolumeCape.Dream.Nimbus l)}{H:Real.exp 1 ≤ Λ.x}
variable {s:ℕ} {i k u v:ℕ→ℕ}
variable {F:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}{P:Playhouse Λ l}
local notation "K"=> tent Y H
local notation "U"=> swept Λ l
local notation "Ω"=> ConeFilter Y i k
variable (W:Traced Y H i k F E P)

-- define all native estate on this physical Y, not tent. even if period-dependent marks defined directly as evaluations!
abbrev Play (Y:Course Λ (VolumeCape.Dream.Nimbus l))(s:ℕ)(i : ℕ→ℕ) := (p:ℕ×ℕ)→ Mark (side Y (i p.1) s)
abbrev fixedPlay (Y:Course Λ (VolumeCape.Dream.Nimbus l))(H:Real.exp 1 ≤ Λ.x)(s:ℕ)(i:ℕ→ℕ)(f:junior (tent Y H)) : Play Y s i := fun p=> observe Y H (i p.1) s f.val

def InHouse (_W:Traced Y H i k F E P) (S:Finset Cover)(f:Play Y s i)(g:junior (tent Y H)):Prop:=
  -- spelling out, since filter eventuallyEq dependent type
  ∃ F':ℕ×ℕ→Palette S,∃ G, Tendsto F' (ConeFilter Y i k) (𝓝 G) ∧ (∀ᶠ p in ConeFilter Y i k,f p= nativeHere Y H (i p.1) s S (F' p)) ∧ music K S G=g

def Sited (W:Traced Y H i k F E P)(f:Play Y s i)(g:junior (tent Y H)) := ∃ S:Finset Cover, InHouse W S f g
namespace InHouse
variable {W}{f h:Play Y s i}{g x:junior (tent Y H)}{S T:Finset Cover}(p:InHouse W S f g)
local notation "L"=> music K

lemma const {g:junior (tent Y H)}(p:g∈club K S): InHouse W S (fixedPlay Y H s i g) g:=by
  obtain ⟨x,rfl⟩:= music_rep K S g p; exact ⟨fun _=>x,x,tendsto_const_nhds,Eventually.of_forall (fun p=> (nativeHere_eq ..).symm),rfl⟩
include p
lemma roomOf : g∈club K S:= by obtain ⟨_,_,_,_,rfl⟩:=p; exact cleft ..
lemma paid : ∀ᶠ a:ℕ × ℕ in ConeFilter Y i k, AtSupport (n:=side Y (i a.1) s) false (Satin.region S (side Y (i a.1) s)) (f a) := by
  obtain ⟨X,x,_,v,_⟩:=p; refine v.mono fun t ht=> Eq.mp ?_ (nativeHere_support Y H (i t.1) s S (X t)); exact congrArg (AtSupport (n:=side Y (i t.1) s) false (region S (side Y (i t.1) s))) ht.symm
lemma unknown (t:∀ᶠ p in ConeFilter Y i k,f p=h p) : InHouse W S h g:=by obtain ⟨f,g,x,v,a⟩:=p; exact ⟨f,g,x,(v.and t).mono (fun i v=> v.2.symm.trans v.1),a⟩
lemma mono (t:S⊆T): InHouse W T f g:=by
  obtain ⟨x,y,g',h,rfl⟩:=p; let w:=featuring K S t; refine ⟨w ∘ x,w y, w.continuous.continuousAt.tendsto.comp g',?_, stow K S t y⟩
  refine h.mono fun j p=> p.trans ?_; simp_rw [nativeHere_eq,← music_coe]; rw [show (w ∘ x) j=featuring K S t (x j) from rfl, stow]

protected lemma add (t:InHouse W S h x) : InHouse W S (f+h) (g+x):=by
  obtain ⟨q,y,hq,v,rfl⟩:=p; obtain ⟨w,z,t,h,rfl⟩:=t; refine ⟨fun x=>q x+w x,y+z,hq.add t, ?_,map_add ..⟩; refine (v.and h).mono (fun i x=> ?_); rw [map_add,Pi.add_apply,x.1,x.2]
protected lemma scale (a:ℂ) : InHouse W S (a • f) (a • g):=by
  obtain ⟨q,y,hq,v,rfl⟩:=p; refine ⟨fun x=>a • q x,a • y,tendsto_const_nhds.smul hq, ?_, map_smul ..⟩; refine v.mono (fun i x=> ?_); rw [map_smul,Pi.smul_apply,x]
protected lemma mul (t:InHouse W S h x) : InHouse W S (f*h) (g*x):=by
  obtain ⟨q,y,hq,v,rfl⟩:=p; obtain ⟨w,z,t,h,rfl⟩:= t; refine ⟨fun x=> chorusMul K S (q x) (w x), chorusMul K S y z, timely_mul K S hq t,?_, con_join ..⟩
  filter_upwards [v,h] with j a b; rw [Pi.mul_apply,a,b]; simp_rw [nativeHere_eq,←music_coe]; rw [con_join]; exact (observe_mul ..).symm -- def after
lemma next : InHouse W (swept Λ l S) (s:=s+1) (fun a=>haul Y s (i a.1) (k a.2) (f a)) (courseAdvance Y H s W g):=by
  obtain ⟨q,y,hq,v,rfl⟩:= p; let w:= fun (a:ℕ×ℕ)=>screen Y H S s (i a.1) (k a.2); let v':=box_visit W.own.pick (S:=S) (s:=s)
  refine ⟨fun a=> w a (q a),_, pair_eval (cone_trace Y H S s W.own P W.receipts) hq, ?_,(courseAdvance_on ..).symm⟩
  filter_upwards [v,v'] with a z b; unfold w; rw [z,house Y H S s b,repertoire]

omit p in
lemma Copies.turn {N P:Side}(h:N=P)(a:Axis)(z:ℤ)(f:Mark N):
    Copies.transport h (reflMark a z f)=reflMark a z (Copies.transport h f) := by subst P; rfl -- omit p

lemma blink (a:Axis)(z:ℤ): InHouse W (shadow a z S) (fun p:ℕ×ℕ=> reflMark a z (f p): Play Y s i) (turn (tent Y H) a z g):=by
  obtain ⟨q,y,hq,v,rfl⟩:=p; let z':=mirrorL K a z S; refine ⟨z'∘q,z' y,z'.continuous.continuousAt.tendsto.comp hq, ?_,(mirror_run ..).symm⟩
  filter_upwards [v] with t p
  rw [p]; simp_rw [nativeHere_eq,← music_coe]; rw [show L _ ((z'∘q) t)= _ from (mirror_run («K»:=K) a z (q t)).symm,turn_coe]; simp_rw [observe_formula]; exact (Copies.turn ..).symm
-- hence any Sited limits of the same family agree.
theorem unique (t:InHouse W S f x): g=x:=by
  obtain ⟨q,y,hq,v,rfl⟩:=p; obtain ⟨w,z,t,h,rfl⟩:=t; letI:= ConeFilter.uses (Y:=Y) (i:=i) W.own.pick.grow_k
  apply congrArg; refine tendsto_nhds_unique_of_eventuallyEq hq t ?_
  filter_upwards [v,h,homes_cone W.own.pick s S] with j a b c
  have ht:= (show native S K _ (q j)=native S K _ (w j) from (Copies.transport (terrain Y H (Y.ir (i j.1)) s)).injective (a.symm.trans b))
  apply native_injective S K _ ht; exact Eq.mp (congrArg (Hosp S) (terrain Y H (Y.ir (i j.1)) s).symm) (roomy c)

lemma whole : Tendsto (fun j:ℕ×ℕ=> Journey.compass Y (i j.1) (k j.2) s (f j)) (ConeFilter Y i k) (𝓝 (E s g.val)):=by
  obtain ⟨q,y,hq,v,rfl⟩:=p
  apply (pair_eval (hear Y H S s W).2 hq).congr'
  filter_upwards [v, ready_cone Y H S s W.own] with j a v; rw [onPitch Y H S s v,a]; rfl
end InHouse
namespace Sited
variable {W}{f h:Play Y s i}{g x:junior (tent Y H)}(p:Sited W f g)
lemma given (f:junior (tent Y H)):Sited W (fixedPlay Y H s i f) f := ⟨_,InHouse.const (supported K f).choose_spec⟩
include p
lemma fortuity (t:∀ᶠ p in ConeFilter Y i k,f p=h p) : Sited W h g:=by obtain ⟨_,p⟩:=p; exact ⟨_,p.unknown t⟩
lemma advancing : Sited W (s:=s+1) (fun a=>haul Y s (i a.1) (k a.2) (f a)) (courseAdvance Y H s W g):= ⟨_, p.choose_spec.next⟩
lemma back_together (t:Sited W f x):g=x:= InHouse.unique (p.choose_spec.mono (T:=p.choose∪t.choose) subset_union_left) (t.choose_spec.mono subset_union_right)
lemma add (t:Sited W h x) : Sited W (f+h) (g+x) := ⟨p.choose∪t.choose,(p.choose_spec.mono subset_union_left).add (t.choose_spec.mono subset_union_right)⟩
lemma mul (t:Sited W h x) : Sited W (f*h) (g*x) := ⟨p.choose∪t.choose,(p.choose_spec.mono subset_union_left).mul (t.choose_spec.mono subset_union_right)⟩
lemma mirror (a:Axis)(z:ℤ): Sited W (s:=s) (fun p=> reflMark a z (f p)) (turn (tent Y H) a z g):=⟨_, p.choose_spec.blink a z⟩
end Sited
end YM.CF.Buffered.Concord
#print axioms YM.CF.Buffered.Concord.InHouse.whole
#print axioms YM.CF.Buffered.Concord.Sited.back_together
