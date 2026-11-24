import Velour.Board.Skim
/-!
# Accounting system for extensive chess

An address denotes a full cubic leaf cell. Forty or 10^40 leaves: no
small-support hypothesis on union. Boxes and mirrors on the COVER, with
wrapped actual costs (to be estimated on the torus).
-/
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxRecDepth 5800
set_option maxHeartbeats 1200000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Buffered.Afterglow.Tower.SlabMark.VelourBoard
open Function Filter Metric NormedSpace SU Lat Lattice Wilson Cube Finset Mir Phase MeasureTheory RP Reflect Advance Nacre Spire Scroll Peaks Rush Tulip Skye Window Vale Girt
open Push.SectorMeasure RG Lifted Scree ProbabilityTheory Py Py.Rate LocalLimit FullBill Sound Common
open scoped Topology Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators Kronecker ComplexOrder NNReal ENNReal Classical
attribute [local instance] opCStarAlgebra
open Preparation Journey Satin Heat Fock Analysis
open SatinVerification

/-- w width in resolution ticks, o i origin (in those ticks).
a i indexes left face of tile. -/
abbrev Cell := Axis→ℤ
variable (K:Calibration) (w:ℕ) (o:Cell)
def Wall (i:Axis)(u:ℤ) := ruler K.B*(o i + w*u)
def PaneCut (i:Axis)(d:ℤ) := ruler K.B*o i + gaugeT K (w*d)
lemma two_cut (i:Axis)(d:ℤ) :
 2*PaneCut K w o i d = 2*(ruler K.B*o i) + ruler K.B*(w*d) :=by
 rw [← ruler_offset K ((w:ℤ)*d)]; unfold PaneCut; ring
lemma across_wall (i:Axis) (d u:ℤ) :
 2*PaneCut K w o i d - Wall K w o i u = Wall K w o i (d-u):=by
 rw [two_cut]; unfold Wall; ring
def Parcel (a:Cell) (S:Finset Cover) : Prop := ∀ i, Between K i (Wall K w o i (a i)) (Wall K w o i (a i+1)) S
def tipped (i:Axis)(d:ℤ)(a:Cell) : Cell := fun j=> if j=i then d-a j-1 else a j


lemma tipped_twice(i:Axis)(d:ℤ) (a:Cell):
 tipped i d (tipped i d a) = a:=by
 ext j; unfold tipped; split_ifs <;> ring
lemma tipped_inj (i:Axis)(d:ℤ) : Injective (tipped i d):= by
 intro a b h; rw [← tipped_twice i d a,h,tipped_twice]
lemma tipping (i:Axis)(d:ℤ){a:Cell}{S:Finset Cover}(h:Parcel K w o a S) :
 Parcel K w o (tipped i d a) (reflectedBox i (PaneCut K w o i d) S) :=by
 intro j; by_cases t:j=i
 · subst j
   have v:=(h i).mirror K i (PaneCut K w o i d)
   rw [across_wall,across_wall] at v
   rw [tipped,if_pos rfl]; convert v using 2 <;> ring
 unfold tipped; rw [if_neg t]
 intro u p; obtain ⟨x,hu,b⟩:=reflect_stays i _ S p
 rw [b j,if_neg t]; exact h j x hu

structure Tile where
 plot: Cell
 leaf: Family K
variable {K}
noncomputable def tumble (i:Axis)(d:ℤ)(T:Tile K):Tile K :=
 ⟨tipped i d T.plot,mirror K i (PaneCut K w o i d) T.leaf⟩
inductive Transit (w:ℕ)(o:Cell)(f:Family K): Tile K→Prop
 | here : Transit w o f ⟨0,f⟩
 | turn {x:Tile K} (h:Transit w o f x)(i:Axis)(d:ℤ) : Transit w o f (tumble w o i d x)

variable {w o}{f:Family K}{S:Finset Cover}{x:Tile K}
lemma stays
 (p:InTest K true S false f)(q:Parcel K w o 0 S)
 (h:Transit w o f x) :
 ∃ T,InTest K true T false x.leaf ∧ Parcel K w o x.plot T:=by
 induction h with
 | here=> exact ⟨_,p,q⟩
 | turn h i d ih=>
   obtain ⟨T,r,s⟩:=ih
   exact ⟨_,axial K i (PaneCut K w o i d) r,tipping K w o i d s⟩
lemma still_paid {C:ℝ} (p:pay f C)(h:Transit w o f x) : pay x.leaf C:=by
 induction h with
 | here=> exact p
 | turn _ _ _ ih=> exact pay_flips K ih _ _

noncomputable def Representation (l:List (Tile K)):Family K := (l.map Tile.leaf).prod
lemma rep_append (l l':List (Tile K)):
 Representation (l++l')=Representation l*Representation l':=by
 simp only [Representation,List.map_append,List.prod_append]
lemma rep_mirror (i:Axis)(d:ℤ) (l:List (Tile K)):
 Representation (l.map (tumble w o i d))=mirror K i (PaneCut K w o i d) (Representation l):=by
 induction l with
 | nil=> exact (mirror_unit ..).symm
 | cons x l ih=>
   change (mirror _ _ _ x.leaf)*Representation (l.map _)=mirror _ _ _ (x.leaf*Representation l)
   rw [ih,mirror_times]

def RangeAt (L U a:Cell) : Prop := ∀ j:Axis,L j≤a j ∧ a j<U j
def cutOver (L:Cell)(i:Axis)(d:ℤ) : Cell := fun j=> if j=i then d else L j

structure Paved (w:ℕ)(o:Cell)(f:Family K)(l:List (Tile K))(L U:Cell) : Prop where
 homes (x:Tile K) : x∈l → Transit w o f x
 sorted: List.Pairwise (fun x y=> x.plot ≠ y.plot) l
 places (x:Tile K): x∈l → RangeAt L U x.plot
lemma pavingMir {l:List (Tile K)}{L U:Cell}(h:Paved w o f l L U)(i:Axis)(d:ℤ):
 Paved w o f (l.map (tumble w o i d)) (cutOver L i (d-U i)) (cutOver U i (d-L i)):=by
 constructor
 · intro x t; obtain ⟨x,r,e⟩:=List.mem_map.mp t; rw [←e]
   exact (h.homes x r).turn i d
 · rw [List.pairwise_map]
   exact h.sorted.imp fun {a b} t=> mt (fun p : tipped i d a.plot=tipped i d b.plot=> tipped_inj i d p) t
 · intro x t; obtain ⟨x,r,e⟩:=List.mem_map.mp t; rw [←e]
   change RangeAt _ _ (tipped i d x.plot)
   intro j; obtain ⟨a,b⟩:= h.places _ r j
   unfold cutOver tipped; by_cases v:j=i
   · subst j; rw [if_pos rfl,if_pos rfl,if_pos rfl]; omega
   rw [if_neg v,if_neg v,if_neg v]; exact ⟨a,b⟩




variable {l l':List (Tile K)}{L U L' U':Cell}
lemma pavingJoin (h:Paved w o f l L U)(h':Paved w o f l' L' U')(i:Axis)
 (d:U i ≤ L' i) (a:∀j,L j ≤ L' j)(b:∀j,U j ≤ U' j):
 Paved w o f (l++l') L U':=by
 constructor
 · exact fun x r=>(List.mem_append.mp r).elim (h.homes x) (h'.homes x)
 · rw [List.pairwise_append]
   refine ⟨h.sorted,h'.sorted,fun x t y v p=>
     not_lt_of_ge (h'.places y v i).1 ?_⟩
   rw [←p]
   exact (h.places x t i).2.trans_le d
 · intro x z j; rcases List.mem_append.mp z with r|r
   · exact ⟨(h.places _ r j).1,(h.places _ r j).2.trans_le (b _)⟩
   · exact ⟨(a _).trans (h'.places _ r j).1,(h'.places _ r j).2⟩
lemma wallMono (j:Axis): Monotone (Wall K w o j) := by
 intro v t h; unfold Wall
 have r:=ruler_gene K.B; gcongr

-- Union stays in rectangle on cover, cost product at every side.
lemma pavingReservation
 (t:InTest K true S false f)(u:Parcel K w o 0 S)
 (h:Paved w o f l L U) :
 ∃ T, InTest K true T false (Representation l)
   ∧ ∀i,Between K i (Wall K w o i (L i)) (Wall K w o i (U i)) T:=by

 induction l with
 | nil=> exact ⟨∅,InTest.one,fun _ _ h=>by simp at h⟩
 | cons x l ih=>
    obtain ⟨T,v,g⟩:= ih ⟨fun y r=>h.homes _ (List.mem_cons_of_mem _ r),
        (List.pairwise_cons.mp h.sorted).2,fun y r=>h.places _ (List.mem_cons_of_mem _ r)⟩
    obtain ⟨D,e,b⟩:= stays t u (h.homes x List.mem_cons_self)
    refine ⟨D∪T,(e.mono subset_union_left).mul (v.mono subset_union_right),?_⟩
    intro i y ey
    rcases mem_union.mp ey with c|c
    · obtain ⟨q,d⟩:=b i y c
      obtain ⟨r,s⟩:=h.places x List.mem_cons_self i
      exact ⟨le_trans (add_le_add_left (wallMono i r) _) q,d.trans (wallMono i (by omega))⟩
    exact g i y c
lemma pavingCost {C:ℝ}(p:pay f C)(h:Paved w o f l L U):pay (Representation l) (C^l.length):=by
 induction l with
 | nil=> exact fun _ _=>by simp [Representation]
 | cons x l ih=>
   rw [List.length_cons,pow_succ']
   exact pay_mul (still_paid p (h.homes x List.mem_cons_self)) (ih ⟨fun y r=>h.homes _ (List.mem_cons_of_mem _ r),
        (List.pairwise_cons.mp h.sorted).2,fun y r=>h.places _ (List.mem_cons_of_mem _ r)⟩)

end YM.CF.Buffered.Afterglow.Tower.SlabMark.VelourBoard

