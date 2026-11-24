import YM.CF.BPress.Locale.Minty
import YM.CF.BPress.Hazel.Harbor
import YM.CF.BPress.Contour.Tiers
/-! distances purchases. -/
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.BPress.Peel
open Function Finset Filter Metric Lattice Wilson RG Push.AbsoluteSums Branch Cube Bands Locale Grid Hazel Wealth Port Weave
open scoped Topology BigOperators Classical
variable {s:Side}{B:BandWidth}{A:Bands s B}{R:Hangar s}{T:Seal (SiteX A R)}{r t:ℕ}
def stem (u:SiteX A R)(r:ℕ):= (bay (shape A R) u r).filter fun v => v.1=u.1
abbrev fixedR : ℕ:=200
def petal (S:Seal (SiteX A R))(r:ℕ):= S.biUnion fun i=> stem i r
abbrev fan : SiteX A R → Seal (SiteX A R):= Contour.Gilt A R fixedR
abbrev hood (v:SiteX A R)(t:ℕ):=bay (shape A R) v t
lemma stem_t (p q:SiteX A R): p∈ stem q r ↔ p.1=q.1∧ delta q.2 p.2 ≤ r:=by
 constructor; · intro a; obtain ⟨p₁,v⟩:=mem_filter.mp a; exact ⟨v,(max_le_iff.mp (show (shape A R).span q p≤r from (bay_mem _).mp p₁)).2⟩
 rintro ⟨v,h⟩; refine mem_filter.mpr ⟨(bay_mem _).mpr (max_le ?_ h),v⟩; rw [v,d_id]; omega
lemma from_stem (p q:SiteX A R)(t:ℕ): p∈ stem q t ↔ p∈hood q t ∧ p.1=q.1:=mem_filter
lemma stem_flip {p q:SiteX A R}(h:p∈ stem q r): q∈stem p r:= (stem_t ..).2 (by obtain ⟨u,v⟩:= stem_t ..|>.1 h; exact ⟨u.symm,(delta_comm ..).le.trans v⟩)
lemma stem_join {x y z:SiteX A R}(h:y∈stem x r)(q:z∈stem y t): z∈stem x (r+t):=by
 obtain ⟨u,v⟩:= (stem_t ..).1 h; obtain ⟨i,a⟩:= (stem_t ..).1 q; exact (stem_t ..).2 ⟨i.trans u,(delta_triangle x.2 y.2 z.2).trans (Nat.add_le_add v a)⟩
lemma stem_mid(x:SiteX A R)(h:r≤ t): stem x r⊆ stem x t:= fun i g=>(stem_t ..).2 ⟨(stem_t ..|>.1 g).1,(stem_t ..|>.1 g).2.trans h⟩
lemma hood_join {p q w:SiteX A R}(v:p∈hood q r)(g:q∈hood w t): p∈ hood w (t+r):= (bay_mem _).mpr (((shape A R).tri _ q _).trans (Nat.add_le_add ((bay_mem _).mp g) ((bay_mem _).mp v)))
lemma hood_flip {p q:SiteX A R}(v:p∈hood q r): q∈hood p r:= (bay_mem _).mpr (((shape A R).sym p q).le.trans ((bay_mem _).mp v))
lemma hood_mid (x:SiteX A R)(h:r≤t): hood x r⊆ hood x t:=fun _ a=>(bay_mem _).mpr (((bay_mem _).mp a).trans h)
lemma tree_stem (x:SiteX A R)(r:ℕ): Grove (shape A R) (stem x r):=by
 let V:= bay (Grid.field 3 R.period) x.2 r; rw [show stem x r= V.image (Prod.mk x.1) from ?_]; swap; · ext i; constructor; intro h; obtain ⟨g,a⟩:= stem_t ..|>.1 h; exact mem_image.mpr ⟨i.2,(bay_mem _).mpr a, Prod.ext g.symm rfl⟩; intro h; obtain ⟨g,a,rfl⟩:= mem_image.mp h; exact (stem_t ..).2 ⟨rfl,(bay_mem _).mp a⟩ -- tune
 have p0:Grove (Grid.field 3 R.period) V:= by refine trunk ((bay_mem _).mpr (show delta x.2 x.2≤r from (delta_same _).le.trans (Nat.zero_le _))) ?_; intro i h; obtain ⟨t,u,p,g,q,l⟩:= Grid.thin x.2 i (bay_mem _|>.mp h); exact orig_sub (rooted p _ g _ q) u
 apply morph _ _ p0 _ _ (?_); intro i _ j _ h; exact (bay_mem _).mp (mem_filter.mp (show (x.1,j)∈stem (x.1,i) 1 from (stem_t ..).2 ⟨rfl,h⟩)).1 -- tune naming
lemma at_petal {u:SiteX A R} : u∈ petal T r ↔ Hazel.Local T r u:=by
 rw [locale_eq A R T]; constructor; · intro p; obtain ⟨v,i,j⟩:=mem_biUnion.mp p; exact ⟨v,i,And.symm (mem_filter.mp j)⟩
 rintro ⟨i,h,v,t⟩; exact mem_biUnion.mpr ⟨i,h,mem_filter.mpr ⟨t,v⟩⟩
lemma stem_home (p:SiteX A R)(r:ℕ): p∈ stem p r:= (stem_t ..).2 ⟨rfl,(delta_same _).le.trans (Nat.zero_le _)⟩
lemma petals : T⊆ petal T r:=fun i p=> mem_biUnion.mpr ⟨i,p,stem_home ..⟩
lemma stem_bay (x:SiteX A R)(r:ℕ): stem x r⊆ bay (shape A R) x r:= filter_subset ..
lemma radial (p l:A.Hcols)(h:l∈columnBall A p r)(v:r≤R.L.val) : own A R l ∈ stem (own A R p) 1:= (stem_t ..).2 (by obtain ⟨a,u⟩:=(column_eq ..|>.1 h); exact ⟨a,tang_rad R _ _ (u.trans v)⟩) -- tune arg
end YM.CF.BPress.Peel
