import YM.SU5.FiniteGaugeData.Marked.Variation.Lining
import YM.SU5.FiniteGaugeData.Marked.Skylight

/-!
# Some cover geometry and stencil projection (exact when the porch and one extra
step inject; no cutting continuity assumed)
-/
set_option autoImplicit false
set_option synthInstance.maxSize 16000
noncomputable section
namespace YM.CF.Buffered.Afterglow.Satin
open Function Filter NormedSpace SU Lat Lattice Cube Finset MeasureTheory RG Wilson Metric
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Classical
open Fock Rush Scroll Peaks Stencil Tenant Tap Tulip Branch Fir Scree Advance Reflect Window Laurent Next.Free Bloch Drapes Spire Lifted Skye Sound Precision Tree Push.SectorMeasure Next.SectorChange
open Common VolumeCape VolumeCape.Atlas VolumeCape.Mesh VolumeCape.Cane VolumeCape.Read
attribute [local instance] opCStarAlgebra
variable (S:Finset Cover)(D:ℕ)
-- enlarging the stencil system exactly one step; can pad links by adding next for heads

def liner := S.biUnion fun a:Cover=>(Lattice.box D).image fun b=> b+a
def tips := S ∪ S.biUnion (fun a:Cover=>(univ:Finset Axis).image (fun i=>a+step i))
lemma liner_here : S⊆liner S D:=fun a p=> mem_biUnion.mpr ⟨a,p,mem_image.mpr ⟨0,by simp [box_test],zero_add _⟩⟩
lemma tips_here {a:Cover}(p:a∈ S): a∈ tips S:=mem_union_left _ p
lemma tips_there {a:Cover}(p:a∈S)(i:Axis): a+step i ∈ tips S:=mem_union_right _ (mem_biUnion.mpr ⟨a,p,mem_image_of_mem _ (mem_univ i)⟩)

variable (n:Side)
abbrev region := S.image (wrap (More n))
lemma linen_contains: halo D (region S n) ⊆ region (liner S D) n:=by
 intro a p
 obtain ⟨b,s,t⟩:=halo_spec.mp p
 obtain ⟨v,k,rfl⟩:=mem_image.1 s
 exact mem_image.mpr ⟨_,mem_biUnion.mpr ⟨v,k,mem_image_of_mem (fun b=>b+v) (Work.E08.lift_mem_box t)⟩,by rw [map_add,wrap_lift,sub_add_cancel]⟩
-- one scaled cover step for next-level cost
lemma next_contains {m:Side}(g:Ratio n m):
 let B := S.image (fun a=> g.count.val • a)
 Advance.padded g (region S n) D ⊆ region (liner B D) m:=by
 intro B
 suffices h : (region S n).image (ratio g).embed= region B m by unfold Advance.padded; rw [h]; apply linen_contains
 unfold region B; rw [image_image,image_image]; exact image_congr fun a _=> Ratio.embed_wrap (ratio g) a

variable {X I:Type*}(C:Side)(K:ℕ→ℝ)
-- lift via a working patch including S, zone around it

abbrev pole (n:Side)(u:S):Seat n:=wrap (More n) (u:Cover)
abbrev stretch :=Prod.map (pole (S:=S) n) (id:Axis→Axis)
def graft (V:LinksC): Pane n:= fun a=>if h:∃ p:S,pole S n p=a.1 then V ((Classical.choose h).val,a.2) else 1
def replant (Z:PairsC):Fields n:=(graft S n Z.1,graft S n Z.2)
lemma graft_b : Measurable (graft S n):=by apply measurable_pi_lambda; intro a; unfold graft; split; exact measurable_pi_apply _; exact measurable_const
lemma replant_b : Measurable (replant S n):= ((graft_b S n).comp measurable_fst).prodMk ((graft_b S n).comp measurable_snd)
set_option maxHeartbeats 300000 in
lemma graft_deal [MeasurableSpace X](F:Courses C S→ X→LinksC)(b:∀u,Measurable (F u))(i:I→ Courses C S) (t:I→ Side)(p:(a:I)→Edge (Seat (t a))):
 Deal (fun (a:I)(x:X)=> graft S (t a) (F (i a) x) (p a):I→X→SU.E):=by
 let A(a:I): Option (↥S × Axis) := if h:∃ v:S,pole S (t a) v=(p a).1 then some (Classical.choose h,(p a).2) else none
 let Q(e:Option (↥S × Axis))(h:Courses C S)(x:X):SU.E:= match e with
   |none=> 1
   |some z=>F h x (z.1,z.2)
 have he(z:Option (↥S × Axis) × Courses C S): Deal (I:=I) (T:=fun _=>SU.E) (fun _=> Q z.1 z.2):=by
    refine deal_of_one (Y:=SU.E) ?_ isCompact_univ (fun _=>Set.mem_univ _)
    obtain ⟨u|u,h⟩:=z; exact measurable_const
    exact (measurable_pi_apply (X:=(fun _ :Edge Cover=>SU.E)) ((u.1:Cover),u.2)).comp (b _)
 refine (Deal.assembly (X:=X) (T:=fun _:I=> SU.E) (fun (z:Option (↥S × Axis) × Courses C S) (_:I)=> Q z.1 z.2) he (fun a=> (A a,i a))).congr ?_
 intro a x; unfold graft
 by_cases h:∃ v:S,pole S (t a) v=(p a).1
 · rw [show (A a,i a)=(some (Classical.choose h,(p a).2), i a) by rw [show A a=_ from dif_pos h],dif_pos h]
 rw [show (A a,i a)=(none, i a) by rw [show A a=_ from dif_neg h],dif_neg h]

def Tipping : Prop:= Set.InjOn (wrap (More n)) (↑(tips (porch C S)):Set Cover)
lemma inject_stretch (p:Tipping S n C):Injective (stretch (porch C S) n) := by
 apply Injective.prodMap _ injective_id; intro x y u
 exact Subtype.ext (p (tips_here _ (show _ from x.property)) (tips_here _ (show _ from y.property)) u)
lemma within (p:Tipping S n C)(a:S)(i:Axis)(V:LinksC): graft S n V (stretch S n (a,i)) = V (a.val,i):=by
 have hx : ∃b:S,pole S n b=(wrap (More n) (a:Cover)):=⟨a,rfl⟩
 simp only [graft,stretch,Prod.map,pole,id_eq]; rw [dif_pos hx]; let b:=Classical.choose hx
 change V ((b:Cover),i)=_
 suffices t:b=a by rw [t]
 exact Subtype.ext (p (tips_here _ (porch_here C S b.property)) (tips_here _ (porch_here C S a.property)) (Classical.choose_spec hx))
lemma laced (p:Tipping S n C)(u:Pane n)(g:Borel.Aerial.Frame n)(w:Read.Wor (More n) C):
 let Z:=replant S n (pairs C K S (chooseCourse C S n w) (crop C S n u g))
 Agrees (region S n) Z.1 u ∧ Agrees (region S n) Z.2 (Dream.sceneQ C K n u (g,w)):=by
 have he (v:LinksC)(t:Pane n)(h:Agrees S v (onC n t)): Agrees (region S n) (graft S n v) t:=by
    rintro ⟨x,i⟩ a b
    obtain ⟨k,v',rfl⟩:=Finset.mem_image.mp a
    obtain ⟨l,hb,u⟩:= Finset.mem_image.mp b
    have h2:k+step i=l:=p (tips_there _ (porch_here C S v') i) (tips_here _ (porch_here C S hb)) (by rw [map_add,wrap_step]; exact u.symm)
    rw [show graft S n v (wrap (More n) k,i)=v _ from within S n C p ⟨k,v'⟩ i v]
    rw [h (k,i) v' (show k+step i∈S from h2.symm ▸ hb)]; exact onC_spec n t (k,i)
 intro Z; obtain ⟨s,r⟩:=scene_pair C K S n u g w
 exact ⟨he _ _ s,he _ _ r⟩
#check Ratio.embed_wrap
