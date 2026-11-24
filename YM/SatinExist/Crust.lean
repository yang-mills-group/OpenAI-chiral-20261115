import YM.SatinExist.Mast
import SatinThinTrees
-- geometry/algorithm of the one-axis long train root. Reusable on other mosaic costs.
set_option autoImplicit false
set_option maxHeartbeats 450000
set_option maxRecDepth 5000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.Biscuit
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common CF.Pannier.Chancel
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis Again
variable {K:Calibration}{N B D:Side}{e T d:ℕ}{p:Site N→Mark B}{g:Mark B→ℂ}{U:ℤ→ℤ}{k:ℕ}(H: GraceA D e T p g U k)
variable (j:Axis) (w:ℤ)(h:0 < w)(Q:Cover)
-- Key posture. Includes orientation independent transverse pin
structure Tile (j:Axis)(Q:Cover)(e T:ℕ)(x y:ℤ)(l:List (Site N)):Prop where
 rule(x':Site N)(hx:x'∈l): ∃ b:ℤ,x+e ≤ b ∧ b+e ≤y ∧ (b:Per (More N))=node x' j
 other(a:Axis)(v:a≠j)(x':Site N)(t:x'∈l): (node x') a=(Q a:Per (More N))
 pair : outdoor T l
variable {x y z:ℤ}{l r:List (Site N)}
lemma Tile.camp(v:ℤ)(M:Tile j Q e T x y l): Tile j Q e T (2*v-y) (2*v-x) (Again.spun j v l):=by
 unfold Again.spun
 constructor
 · intro m t; obtain ⟨m,tb,rfl⟩:= List.mem_map.mp t; obtain ⟨b,p,u,r0⟩:= M.rule m tb
   refine ⟨2*v-b,by omega,by omega,?_⟩; rw [Shape.nodex]; have hp:=across_coord j v (node m); rw [← r0] at hp; apply (sub_eq_iff_eq_add).mp at hp; rw [hp]; push_cast; ring
 · intro a v x t; obtain ⟨x,tb,rfl⟩:=List.mem_map.mp t -- v shadows
   rw [Shape.nodex, show Shape.anon _ N (node x) a =node x a from ?_, M.other a v x tb]
   nth_rw 1 2 [←Rush.nat_true (node x)]; rw [Shape.anno, wrap_here, wrap_here,fling_move,if_neg v.symm] -- tune
 exact List.pairwise_map.mpr (M.pair.imp (by intro x y f; simp only [Shape.nodex,Shape.anon,affine,separation_translate,separation_signed]; exact f))
lemma Tile.west(M:Tile j Q e T x y l)(h:y ≤ x+N.val): upperRoll l ⊆ band N j x e:=by
 intro q t; obtain ⟨q,tb,rfl⟩:= List.mem_map.mp (List.mem_toFinset.mp t); obtain ⟨b,hb,v,r⟩:=M.rule q tb
 rw [band_spec]; change _ ≤ ((node q j) - (x:Per (More N))).val ∧ ((node q j) - (x:Per (More N))).val+_ ≤ _
 rw [← r,← Int.cast_sub]; have hp:0≤ b-x:=by omega
 have hl:(b-x).toNat < (More N).val:=by change _< N.val*2; have hh:0 < N.val:=N.property; omega
 rw [← Int.toNat_of_nonneg hp,Int.cast_natCast,ZMod.val_natCast_of_lt hl]; omega
lemma east_pair {x y z:ℤ} (M:Tile j Q e T x y l)(G:Tile j Q e T y z r)(d:T <2*e)(h:x ≤ y)(v:y≤z)(w:y≤ x+N.val)(f:z≤ y+N.val) : Tile j Q e T x z (l++r):=by
 have hp:2*y-y=y:=by ring
 let V':= Tile.camp j Q y M
 have t:Tile j Q e T y (2*y-x) _:=hp ▸ V'
 refine ⟨?_,?_,List.pairwise_append.mpr ⟨M.pair,G.pair,?_⟩⟩
 · intro i e; rcases List.mem_append.mp e with u|u
   · obtain ⟨k,c,d,y⟩:= M.rule i u; exact ⟨k,c,d.trans v,y⟩ -- h etc
   obtain ⟨k,c,d,y⟩:= G.rule i u; exact ⟨k,le_trans (add_le_add_left h _) c,d,y⟩
 · intro a v k t; exact (List.mem_append.mp t).elim (M.other a v k) (G.other a v k)
 intro X A Y B; rw [separation_comm]; refine lt_of_lt_of_le d (opposite_gap j y (by omega : 0<e) _ _ ((Tile.west j Q G f) (List.mem_toFinset.mpr (List.mem_map_of_mem B))) ?_); apply mem_image.mpr
 let u:= Shape.mills (plane j y) N X
 have he:u∈ Again.spun j y l:=List.mem_map_of_mem A
 exact ⟨node u,(Tile.west j Q t (by omega)) (List.mem_toFinset.mpr (List.mem_map_of_mem he)),by change Shape.anon (plane j y) N (node ((plane j y).mills N X))= node X; rw [Shape.nodex,fling_there]⟩

-- formal reader. Calendar tick gain R
variable (R:ℤ) (u:∀ s:ℤ,U s=R*s)(L:Family K→Mark B)
variable (Lm: ∀ X Y:Family K,L (X*Y)= L X * L Y)(Lt:L 1=1)(Lf:∀ (s:ℤ)(X:Family K), L (mirror K j (U s) X)=reflMark j (U s) (L X))
def Foot (j:Axis)(Q:Cover)(p:Site N→Mark B)(e T:ℕ)(x y:ℤ)(L:Family K→Mark B)(m:ℕ)(X:Family K) : Prop := ∃ l:List (Site N),Tile j Q e T x y l ∧ l.length=m ∧ L X=(l.map p).prod
local notation "A="=> Foot j Q p e T
variable {m n:ℕ}{X Y:Family K}
include H
include Lm
lemma Foot.pack (M:Foot j Q p e T x y L m X)(G:Foot j Q p e T y z L n Y)(h:x ≤ y)(u:y ≤z)(v:y≤ x+N.val)(w:z≤ y+N.val) : A= x z L (m+n) (X*Y) := by
 -- Lm use
 obtain ⟨l,t,r,s⟩:= M; obtain ⟨r',t',h',q⟩:= G
 refine ⟨_,east_pair j Q t t' H.gap h u v w,by rw [List.length_append,r,h'],?_⟩
 rw [Lm,s,q,List.map_append,List.prod_append]
include Lf
omit Lm
lemma Foot.recur (M:Foot j Q p e T x y L m X)(b:ℤ) : A= (2*b-y) (2*b-x) L m (mirror K j (U b) X):=by
 obtain ⟨l,t,r,s⟩:=M; exact ⟨_,Tile.camp j Q b t,by rw [Again.spun,List.length_map,r],by rw [Lf,s,spun_price H]⟩
include u
lemma Foot.shim(M:Foot j Q p e T x y L m X)(b:ℤ): A= (ruler K.B*b+x) (ruler K.B*b+y) L m (relocate K j (R*b) X):=by
 let V:= Foot.recur H j Q L Lf M 0
 let W:= Foot.recur H j Q L Lf V (gaugeT K b)
 have z: U (gaugeT K b)= gaugeT K (R*b):=by rw [u]; unfold gaugeT Heat.gaugeShift; ring
 rw [z,u 0,mul_zero (R:ℤ)] at W
 have d:2*(gaugeT K b)=ruler K.B*b:=ruler_offset ..; simp only [Int.mul_zero, Int.zero_sub, d, sub_neg_eq_add] at W
 exact W
include h
local notation "t!"=> ruler K.B*w
lemma yacht (M:Foot j Q p e T 0 (t!) L 1 X): A= 0 (t!) L 1 (toward K j (R*w) X n):=by
 induction n with
 | zero=> exact M
 | succ n ih=>
    have W:= Foot.recur H j Q L Lf ih (gaugeT K w);
    rw [u, show R * gaugeT K w=gaugeT K (R*w) from (by unfold gaugeT Heat.gaugeShift; ring),ruler_offset,sub_self,sub_zero] at W; exact W
include Lm Lt
lemma craft (M:Foot j Q p e T 0 (t!) L 1 X)(v:t! * n ≤ (N.val:ℤ)): A= 0 (t!*n) L n (lace K j (R*w) X 1 n):=by
 have he:0<t!:=mul_pos (ruler_gene _) h
 induction n with
 | zero=> refine ⟨[],⟨fun _ f=>(List.not_mem_nil f).elim,fun i h x v=>(List.not_mem_nil v).elim,by simp [outdoor]⟩,rfl,?_⟩; exact Lt
 | succ n ih=>
    rw [Nat.cast_add_one] at v
    have hv:= ih (by nlinarith)
    have W:= Foot.shim H j Q R u L Lf hv w; rw [add_zero] at W
    let B:=Foot.pack H j Q L Lm (yacht H j w h Q R u L Lf M (n:=n)) W he.le (le_add_of_nonneg_right (by positivity)) (by nlinarith) (by linarith)
    convert B using 1 <;> (first | rfl | (push_cast; ring) | omega)
-- M extends time by outward
lemma trail (M:Foot j Q p e T 0 (t!) L 1 X)(v:2*(t!*n) ≤ (N.val:ℤ))(b:ℤ): ∃ (l:List (Site N)), outdoor T l ∧ l.length=4*n ∧ L (banner j (R*w) (R*b) n X)=(l.map p).prod ∧ ∀ a:Axis,a≠j→ cows a (upperRoll l) 0 := by
 let d:= t!*n; let t:= ruler K.B*b
 have he: 0<t!:= mul_pos (ruler_gene _) h; have hv:0≤d:=by unfold d; positivity
 have hp:=craft H j w h Q R u L Lm Lt Lf M (n:=n) (by nlinarith)
 have hs:= Foot.recur H j Q L Lf hp 0; rw [u 0,mul_zero, mul_zero, zero_sub,sub_self] at hs -- order tune
 have hz:2*d ≤ N.val:=v
 have G₀:=Foot.pack H j Q L Lm hs hp (by linarith) hv (by linarith) (by linarith);
 have W:= Foot.shim H j Q R u L Lf G₀ b
 let z:=t-d
 change A= (t+ -d) (t+d) L (n+n) (chambers j (R*w) (R*b) X 1 n) at W
 rw [←sub_eq_add_neg] at W
 have U':= Foot.recur H j Q L Lf W z
 have d':2*z - (t-d)=t-d:=by unfold z; ring
 have p₁:2*z-(t+d)≤t-d:=by unfold z; linarith
 have p₂:t-d≤2*z-(t+d)+N.val:=by unfold z; linarith
 rw [d'] at U'
 obtain ⟨l,k,ht,hm⟩:= Foot.pack H j Q L Lm U' W p₁ (by linarith) p₂ (by linarith)
 have y: U z= gaugeT K (cliff (R*w) (R*b) n):=by rw [centered_index,u]; unfold z t d; ring
 refine ⟨l,k.pair,by omega,by rw [y] at hm; exact hm,fun i v=>?_⟩
 refine ⟨Q i,fun x p=>?_⟩; obtain ⟨x,q,rfl⟩:=List.mem_map.mp (List.mem_toFinset.mp p); exact ⟨Q i,le_rfl,by simp,(k.other i v _ q).symm⟩
end YM.CF.Buffered.Afterglow.Tower.SlabMark.Biscuit
