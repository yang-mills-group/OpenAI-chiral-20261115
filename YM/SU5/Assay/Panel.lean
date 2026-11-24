import YM.SU5.FiniteGaugeData.Tower.Roomer
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6000
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Fock
namespace Etch

-- Cover-of-tiles address (one more copy of Cover), with arbitrary tick offsets σ
-- for checker start. No quotienting.
def pet (x:Cover)(i:Axis)(a:ℤ):Cover:=fun j=>if j=i then a else x j
@[simp] lemma pet_i (x:Cover)(i:Axis)(a:ℤ): pet x i a i=a:=by simp [pet]
lemma pet_j (x:Cover){i j:Axis}(h:j≠i)(a:ℤ): pet x i a j=x j:=by simp [pet,h]
lemma petID (x:Cover)(i:Axis): pet x i (x i)=x:=by funext j; by_cases h:j=i <;> simp [pet,h]
def pushed (i:Axis)(v:ℤ)(x:Cover):Cover:=pet x i (x i+v)
def bent (i:Axis)(v:ℤ)(x:Cover):Cover:=pet x i (v-x i-1)
lemma pushedInj (i:Axis)(v:ℤ): Injective (pushed i v):=by
 intro x y h; funext j
 have ht:=congrFun h j
 unfold pushed at ht
 by_cases a:j=i
 · subst j; rw [pet_i,pet_i] at ht; omega
 rwa [pet_j _ a,pet_j _ a] at ht
lemma bentInj (i:Axis)(v:ℤ): Injective (bent i v):=by
 intro x y h; funext j
 have ht:=congrFun h j
 unfold bent at ht
 by_cases a:j=i
 · subst j; rw [pet_i,pet_i] at ht; omega
 rwa [pet_j _ a,pet_j _ a] at ht

def Inbox (l h:Cover)(x:Cover):Prop:=∀i,l i≤x i∧x i<h i

variable (K:Calibration)(w:ℤ)(σ:Cover)
local notation "ρ" => ruler K.B
noncomputable def runnel (i:Axis)(a:ℤ):=ruler K.B * (σ i + w*a)
/-- Plane for tiling v mirror, in gauge sites. -/
noncomputable def parting (i:Axis)(v:ℤ):=gaugeT K (2*σ i+w*v)
local notation "r" => runnel K w σ
local notation "p" => parting K w σ
lemma parting_edge (i:Axis)(v:ℤ):p i (2*v)=r i v:=by
 have ht:= ruler_offset K (2*σ i+w*(2*v))
 unfold parting runnel; linarith only [ht]

/-- Independent motions. Includes internal tile toggles. -/
inductive Located (K:Calibration)(w:ℤ)(σ:Cover)(f:Family K):Cover→Family K→Prop
| start:Located K w σ f 0 f
| go {x:Cover}{F:Family K}(i:Axis)(v:ℤ)(h:Located K w σ f x F): Located K w σ f (pushed i v x) (relocate K i (w*v) F)
| reflect {x:Cover}{F:Family K}(i:Axis)(v:ℤ)(h:Located K w σ f x F): Located K w σ f (bent i v x) (mirror K i (parting K w σ i v) F)

/-- Cubical tile controls the whole intrinsic support, buffers included. -/
def House (x:Cover)(S:Finset Cover):Prop:=∀i,Between K i (r i (x i)) (r i (x i+1)) S
variable {S:Finset Cover}{x:Cover}
lemma House.go (h:House K w σ x S)(i:Axis)(v:ℤ): House K w σ (pushed i v x) (plow K i (w*v) S):=by
 intro j
 by_cases a:j=i
 · subst j
   unfold pushed; rw [pet_i]; convert Between.relocate K i (h i) (w*v) using 1 <;> unfold runnel <;> ring
 intro t u
 obtain ⟨y,g,rfl⟩:=plow_stays K i (w*v) S u; unfold pushed; rw [moves,if_neg a,pet_j _ a]; exact h j y g
lemma House.reflect (h:House K w σ x S)(i:Axis)(v:ℤ): House K w σ (bent i v x) (reflectedBox i (p i v) S):=by
 intro j
 by_cases a:j=i
 · subst j
   unfold bent; rw [pet_i]; convert Between.mirror K i (h i) (p i v) using 1 <;> unfold runnel parting <;> rw [ruler_offset] <;> ring
 intro t u
 obtain ⟨y,g,e⟩:=reflect_stays i (p i v) S u; unfold bent; rw [e,if_neg a,pet_j _ a]; exact h j y g

variable {f F G:Family K}
lemma Located.receives {A:ℝ}(h:InTest K true S false f)(u:House K w σ 0 S)(c:pay f A) (z:Located K w σ f x F):
 (∃T:Finset Cover,InTest K true T false F ∧ House K w σ x T)∧pay F A:=by
 induction z with
 | start=>exact ⟨⟨S,h,u⟩,c⟩
 | go i v _ e=>obtain ⟨⟨T,h,g⟩,t⟩:=e; exact ⟨⟨_,flow_port K i _ h,g.go _ _ _ i v⟩,chime_pay _ _ _ _ t⟩
 | reflect i v _ e=>obtain ⟨⟨T,h,g⟩,t⟩:=e; exact ⟨⟨_,axial K i _ h,g.reflect _ _ _ i v⟩,pay_flips K t i _⟩

abbrev Grain (K:Calibration):Type:=Cover × Family K
def castings (L:List (Grain K)):Family K:=(L.map Prod.snd).prod
local notation "M"=>castings K

/-- Lay down n terms, order explicit. Upper tile bound exclusive as for Inbox. -/
def Panel (f:Family K)(l h:Cover)(n:ℕ)(F:Family K):Prop:=∃ L:List (Grain K),
    L.length=n ∧ (∀ a∈L,Inbox l h a.1∧Located K w σ f a.1 a.2) ∧
    L.Pairwise (fun a b=> a.1≠b.1) ∧ M L=F
variable {l h:Cover}{n m:ℕ}
local notation "P"=>Panel K w σ

lemma Panel.blank :P f l h 0 1:=by
 refine ⟨[],rfl,by simp,by simp,?_⟩; rfl
lemma Panel.single (t:Inbox l h x)(v:Located K w σ f x F):P f l h 1 F:=by
 refine ⟨[(x,F)],rfl,?_,by simp,?_⟩
 · simpa only [List.forall_mem_singleton] using And.intro t v
 simp [castings]

-- General motion, sends disjointness by injectivity
lemma Panel.moves (z:P f l h n F)(u v:Cover)(g:Cover → Cover)(k:Family K→Family K)
 (i:Injective g)(ij:∀x,Inbox l h x→Inbox u v (g x))(hL:∀x a,Located K w σ f x a→Located K w σ f (g x) (k a))
 (h1:k 1=1)(ht:∀a b,k (a*b)=k a*k b):P f u v n (k F):=by
 let t:Grain K→Grain K:=fun x=> (g x.1,k x.2)
 obtain ⟨L,rfl,hx,hP,rfl⟩:=z
 refine ⟨L.map t,List.length_map ..,?_,List.pairwise_map.mpr ?_,?_⟩
 · intro a ha; obtain ⟨b,hb,rfl⟩:=List.mem_map.mp ha
   exact ⟨ij _ (hx b hb).1,hL _ _ (hx b hb).2⟩
 · exact hP.imp (fun hz e=>hz (i e))
 · clear hx hP; induction L with
   | nil=> exact h1.symm
   | cons a L ih=>
     change k a.2 * (M (L.map t)) = k (a.2 * (M L))
     rw [ih,ht]

lemma Panel.forward (i:Axis)(v:ℤ){b d:ℤ}(z:P f (pet l i b) (pet h i d) n F):
 P f (pet l i (b+v)) (pet h i (d+v)) n (relocate K i (w*v) F):=by
 refine z.moves _ _ _ _ _ (pushed i v) (relocate K i (w*v)) (pushedInj i v) ?_ (fun _ _ a=>Located.go i v a) (relocate_unit ..) (fun _ _=>relocate_mul ..)
 intro x a j; specialize a j; unfold pushed
 by_cases t:j=i
 · subst j; simp only [pet_i] at *; omega
 simpa only [pet_j _ t] using a

lemma Panel.turn (i:Axis)(v:ℤ){b d:ℤ}(z:P f (pet l i b) (pet h i d) n F):
 P f (pet l i (v-d)) (pet h i (v-b)) n (mirror K i (p i v) F):=by
 refine z.moves _ _ _ _ _ (bent i v) (mirror K i (p i v)) (bentInj i v) ?_ (fun _ _ a=>Located.reflect i v a) (mirror_unit ..) (fun _ _=>mirror_times ..)
 intro x a j; specialize a j; unfold bent
 by_cases t:j=i
 · subst j; simp only [pet_i] at *; omega
 simpa only [pet_j _ t] using a

lemma Panel.glue (i:Axis){a b c:ℤ}(t:a≤b)(v:b≤c)(z:P f (pet l i a) (pet h i b) n F)(y:P f (pet l i b) (pet h i c) m G):
 P f (pet l i a) (pet h i c) (n+m) (F*G):=by
 obtain ⟨L,rfl,hL,hP,rfl⟩:=z; obtain ⟨J,rfl,hJ,hQ,rfl⟩:=y
 refine ⟨L++J,List.length_append,?_,List.pairwise_append.mpr ⟨hP,hQ,?_⟩,by simp [castings]⟩
 · intro x e; rcases List.mem_append.mp e with xL|xJ
   · obtain ⟨e,g⟩:=hL x xL; refine ⟨?_,g⟩
     intro j; specialize e j; by_cases d:j=i
     · subst j; simp only [pet_i] at *; omega
     simpa only [pet_j _ d] using e
   · obtain ⟨e,g⟩:=hJ x xJ; refine ⟨?_,g⟩
     intro j; specialize e j; by_cases d:j=i
     · subst j; simp only [pet_i] at *; omega
     simpa only [pet_j _ d] using e
 · intro x h₁ y h₂ e
   have u:=(hL x h₁).1 i; have g:=(hJ y h₂).1 i; simp only [pet_i] at u g; rw [e] at u; omega

lemma runnelMono
 (hw:0≤w)(i:Axis){a b:ℤ}(v:a≤b): r i a≤r i b:=by
 have hr:0≤ρ:=(ruler_gene _).le
 unfold runnel; gcongr

/-- Support and pay for the whole panel. -/
lemma Panel.receives {A:ℝ}(hw:0≤w)(e:InTest K true S false f)(u:House K w σ 0 S)(c:pay f A)
 (z:P f l h n F):
 (∃T:Finset Cover,InTest K true T false F ∧ ∀i,Between K i (r i (l i)) (r i (h i)) T)∧pay F (A^n):=by
 obtain ⟨L,rfl,H,H0,rfl⟩:=z; clear H0
 induction L with
 | nil=>
   refine ⟨⟨∅,InTest.one,fun i v t=>by simp at t⟩,?_⟩
   rw [List.length_nil,pow_zero]; exact pay_unit
 | cons a L ih=>
   obtain ⟨⟨T,hT,b⟩,d⟩:= ih (fun x g=>H x (List.mem_cons_of_mem _ g))
   obtain ⟨hp,t⟩:=H a (by simp)
   obtain ⟨⟨U,hU,k⟩,v⟩:= t.receives _ _ _ e u c
   rw [List.length_cons,pow_succ']
   refine ⟨⟨U∪T,(hU.mono subset_union_left).mul (hT.mono subset_union_right),?_⟩,pay_mul v d⟩
   intro i x hx
   rcases mem_union.mp hx with hx | hx; swap; · exact b i x hx
   obtain ⟨hh,hy⟩:=k i x hx
   have h₁:=runnelMono K w σ hw i (hp i).1; have h₂:=runnelMono K w σ hw i (show a.1 i+1≤h i by exact Int.add_one_le_of_lt (hp i).2)
   constructor <;> omega
end Etch
end YM.CF.Buffered.Afterglow.Tower.SlabMark
