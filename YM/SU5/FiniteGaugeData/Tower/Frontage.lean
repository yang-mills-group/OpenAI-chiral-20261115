import YM.SU5.FiniteGaugeData.Tower.Veranda
/-!
# Estimating moments from a single finite-jitter layout (at limiting E, no width changes)

Each time schedule using jitter of size n and separation growing much faster.
Average over entire experiment. Grammatical calculations for hypotheses
we need (arity-variable).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 6500
set_option maxHeartbeats 360000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.Vacancy
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder InnerProductSpace NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis SlabMark OS.Semigroup MeshClock Set
section select
variable {S:Type*}[Fintype S]
-- jitter organizer, peel out time j everywhere (relative gates chosen afterward)
-- Fin n+1 allows n=0
abbrev agent(n:ℕ) := S→ Axis → Fin (n+1)
abbrev clerk(n:ℕ)(j:Axis):= S→ Trans j→ Fin (n+1)
def forum(j:Axis)(n:ℕ)(q:S→Fin (n+1))(p:clerk (S:=S) n j)(i:S)(s:Axis):Fin (n+1):=if h:s=j then q i else p i ⟨s,h⟩
lemma meeting(j:Axis)(n:ℕ)(f:agent (S:=S) n→ℂ):Average.center f=
 Average.center (fun t:S→Fin (n+1)=>Average.center (fun p:clerk (S:=S) n j=> f (forum j n t p))):=by
 let T: ((S→Fin (n+1)) × (clerk n j)) ≃ agent (S:=S) n:= {
    toFun x:=forum j n x.1 x.2
    invFun x:=⟨fun i=>x i j,fun i s=> x i s.1⟩
    left_inv x:=by
       apply Prod.ext -- functions on S etc
       · funext i; simp [forum]
       funext i a; simp [forum,a.property]
    right_inv x:=by funext i s; dsimp only; unfold forum; split <;> simp_all }
 rw [← Average.trade T,Average.domino]; rfl
-- for generator moment tests. preserve absolute positions when changing axes.
noncomputable def pins (q:S→Axis→ℕ)(i:ℕ)(x:agent (S:=S) i)(t:S)(a:Axis):ℤ:= 3*q t a*i+(x t a).val
-- generate lengths recursively following order (hyp l.Pairwise j t).
noncomputable def markers (Rise:S→ℤ)(Size:S→ℕ)(p:S→ Cover)(j:Axis): ℤ → List S → S→ℕ
 | b,[]=>0
 | b,i::l=>Function.update (markers Rise Size p j (p i j-Rise i+Size i) l) i (p i j-Rise i-b).toNat
-- starting b=-i^2 maybe cost. need incoming relation
private lemma clocks (rise:S→ℤ)(size:S→ℕ)(d:S→ Cover)(j:Axis)
 (q:ℕ)(l:List S)(h:l.Nodup)(p:l.Pairwise (fun i x=> (d i j-rise i+size i)+q≤ d x j-rise x))(s:ℤ)(u:∀i∈l,s+q≤d i j-rise i):∀ i∈l,q ≤ markers rise size d j s l i:=by
 induction l generalizing s with
 | nil => simp
 | cons i l ih=>
    obtain ⟨hv,hl⟩:=List.pairwise_cons.mp p; obtain ⟨fx,ha⟩:=List.nodup_cons.mp h
    intro k e; rcases List.mem_cons.mp e with rfl|e <;> rw [markers] 
    · rw [Function.update_self]; have he:=u k (List.Mem.head ..); omega
    rw [Function.update_of_ne (show k≠i from fun u=>fx (u ▸ e))]; exact ih ha hl (d i j-rise i+size i) hv _ e
-- pad orders at any pinning via chosen label ordering.
lemma strong_order(j:Axis)(q:S→Axis→ℕ)(l:List S)(t:l.Pairwise (fun i k=>q i j < q k j))(rise:S→ℤ)(size:S→ℕ):
 ∀ᶠ n:ℕ in atTop,∀p:agent (S:=S) n,
 l.Pairwise (fun i x=> (pins q n p i j-rise i+size i)+n≤ pins q n p x j-rise x) ∧ ∀i∈l, -(2*(n:ℤ))+n ≤ pins q n p i j-rise i :=by
 have hx(i x:S):∀ᶠ n:ℕ in atTop,∀p:agent (S:=S) n,q i j<q x j → pins q n p i j-rise i+size i+n≤ pins q n p x j-rise x:=by
    filter_upwards [eventually_ge_atTop (size i+ (rise i).natAbs+(rise x).natAbs)] with n h p k
    have h':(p i j).val≤ n:=Nat.le_of_lt_succ (Fin.isLt _)
    have hv:(q i j+1:ℕ)≤q x j:=by omega
    have hm:((q i j+1:ℕ):ℤ)≤ ↑(q x j):=by exact_mod_cast hv
    unfold pins
    have hp : -((rise i).natAbs:ℤ) ≤ rise i:=by omega
    have hs : rise x ≤ ((rise x).natAbs:ℤ):=by omega
    push_cast at hm; zify at h h'; nlinarith [mul_le_mul_of_nonneg_right hm (show (0:ℤ)≤3*(n:ℤ) by positivity),neg_le_abs (rise i),le_abs_self (rise x)]
 have ht (i:S):∀ᶠ n:ℕ in atTop,∀p:agent (S:=S) n,-(2*(n:ℤ))+n ≤ pins q n p i j-rise i:=by
    filter_upwards [eventually_ge_atTop (rise i).natAbs] with n h p
    have ht:rise i ≤ (n:ℤ):=by omega
    unfold pins; nlinarith
 filter_upwards [(eventually_all_finset l.toFinset).mpr (fun i _=>ht i),(eventually_all_finset univ).mpr (fun (p:S×S) _=> hx p.1 p.2)] with n v h p
 exact ⟨t.imp (fun {i q} k=> h (i,q) (mem_univ _) _ k), fun i z=>v i (by simpa using z) _⟩
end select

variable {Λ:Preparation}{lp:ℕ}(Y:Course Λ (VolumeCape.Dream.Nimbus lp))(H:Real.exp 1≤Λ.x)
local notation "K"=>tent Y H
variable {i k:ℕ→ℕ}{I:ℕ→Family (tent Y H)→ℕ→ℂ}{E:ℕ→Family (tent Y H)→ℂ}(V:Universal Y H i k I E)(s:ℕ)
variable {D:ℕ→Family (tent Y H)→Family (tent Y H)}{a b:ℕ→ℕ}(Q:Coherent (i:=i) (k:=k) (E:=E) Y H D a b)(Qt:Clipped Y H (i∘a) (k∘b))
variable (j:Axis)(strict:Bool)(C:Arena Y H Q.circuit j 0 strict)
local notation "A"=>Ark.Ht Y H Q.circuit j 0 strict C
local notation "S₀" s:max=> office Y H V s Q j strict C
local notation "W"=>floorV Y H Q.circuit j 0 strict C
local notation "D₀" s:max=> Console.sky (S₀ s) (look j)
variable {S:Type*}[Fintype S](X:S→ observable (tent Y H) strict)(Z:∀i,Veranda Y H s j strict (X i))
local notation "Vs" i:max=>Veranda.placed Y H V s Q Qt j strict C (Z i)
local notation "sz"=> fun i=>(Z i).span
local notation "R"=>fun i=>(Z i).rise
private lemma weaken {p:S→ Cover}{u v:S→ℕ}{l:List S}(h:∀i∈l,u i=v i){b:ℤ}(q:Weaves Y H s j strict X Z p u l b):Weaves Y H s j strict X Z p v l b:=by induction l generalizing b with
| nil=>exact q
| cons i l ih=> obtain ⟨a,c⟩:=q; let he:=h i (List.Mem.head ..); exact ⟨he ▸ a,he ▸ ih (fun i e=> h i (List.Mem.tail _ e)) c⟩
private lemma can_move(n:ℕ)(P:S→ Cover)(l:List S)(t:l.Nodup)(u:l.Pairwise (fun i x=> (P i j-(R) i+(sz) i)+n≤ P x j-(R) x))(b:ℤ)(h:∀i∈l,b+n≤P i j-(R) i):
 Weaves Y H s j strict X Z P (markers R sz P j b l) l b:=by induction l generalizing b with
 | nil=>trivial
 | cons i l ih=>
    obtain ⟨f,t⟩:=List.nodup_cons.mp t; obtain ⟨U,p⟩:= List.pairwise_cons.mp u
    rw [Weaves,markers,Function.update_self]
    have h':b+n ≤ P i j-(Z i).rise:=h i (List.Mem.head ..)
    constructor
    · omega
    rw [show b+(((P i j-(Z i).rise-b).toNat):ℤ)+(Z i).span=P i j-(Z i).rise+(Z i).span by omega]
    apply weaken Y H s j strict X Z ?_ (ih t p _ U)
    intro v hv; rw [Function.update_of_ne (show v ≠ i from fun h=>f (h ▸ hv))]
-- limiting arrangement along one axial order. other coordinates can move arbitrarily by this rule.
noncomputable def innerAth (l:List S):ℂ:= inner ℂ W (Average.ordered l (fun i=>(D₀ s).comp (Vs i)) W)
noncomputable def outerAth (q:S→Axis→ℕ)(l:List S)(n:ℕ):ℂ:= Average.center (fun i:agent (S:=S) n=> E s (score Y H strict X (pins q n i) l))
private lemma coreC {S:Type*} {f g:Fintype S} {XH:Hilbert}(L:XH→L[ℂ]ℂ)(F:S→ XH)(Wt:S→ℂ)(h:∀i,L (F i)=Wt i):L (@Average.center S f XH _ _ F)= @Average.center S g ℂ _ _ Wt:=by cases Subsingleton.elim g f; letI:=f; exact (Average.natural F L).symm.trans (Average.eq_of _ _ h)
lemma consensus(q:S→Axis→ℕ)(L:List S)(h:L.Nodup)(t:L.Pairwise (fun i k=>q i j < q k j)):
 Tendsto (outerAth Y H (E:=E) s strict X q L) atTop (𝓝 (innerAth Y H V s Q Qt j strict C X Z L)):=by
 unfold outerAth; simp_rw [meeting j]
 apply Average.by_choice
 intro y
 let pin(n:ℕ)(v:clerk (S:=S) n j):= pins q n (forum j n (y n) v)
 let b(n:ℕ):= -(2*(n:ℤ))
 let q0(n:ℕ)(x:S)(a:Axis):ℤ:=3*q x a*n+(y n x).val -- only j key
 let U(i:S)(n:ℕ):= if i∈L then markers R sz (q0 n) j (b n) L i else n
 have ht(n:ℕ)(x:S)(v:clerk (S:=S) n j): pin n v x j=q0 n x j:=by simp [pin,pins,q0,forum]
 have hv :∀ᶠ n:ℕ in atTop, L.Pairwise (fun i x=> (q0 n i j-(R) i+(sz) i)+n≤ q0 n x j-(R) x)∧ ∀i∈L, b n+n≤q0 n i j-(R) i :=by
    filter_upwards [strong_order j q L t R sz] with n k
    have hk:= k (forum j n (y n) (fun _ _=>0)); simpa [pins,forum,q0,b] using hk
 have he(i:S): Tendsto (U i) atTop atTop:=tendsto_atTop_mono' _ (hv.mono (fun n a=> by
    change n ≤ if _ then _ else _; split
    next hp=>exact clocks R sz _ _ n L h a.1 _ a.2 i hp
    next=> exact le_refl _)) (Filter.tendsto_id) -- id wrong
 let D(i:S)(n:ℕ)(a:Trans j):ℤ:=3*(q i a.val)*n
 let T:=S₀ s
 let Q' := (T).train (look j) (look_one j) L h (fun i=> Vs i) U he D W (occupant Y H V s Q j strict C)
 apply (((innerSL ℂ W).continuous.continuousAt (x:=_)).tendsto.comp Q').congr'
 filter_upwards [hv] with n hV
 apply coreC (L:=innerSL ℂ W); intro k 
 let X0:= pin n k
 have hw:=hV.1; have h0k:=hV.2 -- remove slash
 have ha: L.Pairwise (fun i x=> (X0 i j-(R) i+(sz) i)+n≤ X0 x j-(R) x)∧ ∀i∈L,b n+n ≤X0 i j-(R) i := by unfold X0; simp_rw [ht]; exact hV
 have hb:=can_move Y H s j strict X Z n X0 L h ha.1 (b n) ha.2
 have hj {l:List S}(Kk:ℤ):markers R sz X0 j Kk l=markers R sz (q0 n) j Kk l:=by
    induction l generalizing Kk with
    | nil=>rfl
    | cons i z ih=>rw [markers,markers,show X0 i j=q0 n i j from ht n i k,ih]
 rw [hj] at hb
 have hB:=weaken Y H s j strict X Z (v:=fun i => U i n) (fun i v=> (if_pos v).symm) hb
 have hw:= attains Y H V s Q Qt j strict C X Z X0 L (b n) (fun i=>U i n) hB
 have hO (s:S):Moving.crew n (D s n) (k s) = fun i:Trans j=> X0 s i.val:=by funext i; unfold Moving.crew D X0 pin pins; simp [forum,i.property]; -- ring?
 simp_rw [hO]; exact hw

end YM.CF.Buffered.Afterglow.Tower.Vacancy
#print axioms YM.CF.Buffered.Afterglow.Tower.Vacancy.consensus
