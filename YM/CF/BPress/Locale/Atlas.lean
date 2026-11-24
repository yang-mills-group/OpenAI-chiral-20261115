import YM.CF.BPress.Locale.Parcel
import YM.CF.BPress.Weave.Turf
/-!
Tangential `Λ` block and ambient log reads. counts, connects, rates. -/
set_option autoImplicit false
noncomputable section
namespace YM.CF.BPress.Locale
open Function Filter Finset Lattice Wilson RG Grid Branch Cube Bands Tunnel Wealth Weave Radix
open scoped Topology BigOperators Classical Matrix
variable {s :Side}{b:BandWidth}(X:Bands s b)
structure Hangar (s:Side) where
 L: Side
 period : Side
 geom : s.val=L.val*period.val
variable (R:Hangar s)
abbrev SiteX := X.Index × Tri R.period
def shape : Branch.Field (SiteX X R) where
 span x y:= max (delta1 X.Q x.1 y.1) (delta x.2 y.2)
 reflex x:= by rw [d_id,delta_same]; simp
 sym x y:= by rw [d_sym,delta_comm]
 tri x y z:= max_le (le_trans (d_one_triangle _ y.1 _) (add_le_add (le_max_left ..) (le_max_left ..))) (le_trans (delta_triangle x.2 y.2 z.2) (add_le_add (le_max_right ..) (le_max_right ..)))
def tang (x:Tri s): Tri R.period:= fun i=>idx R.geom 0 (x i)
abbrev own (x:X.Hcols) : SiteX X R:= (x.1,tang R x.2)
def plan (x:Site s) := own X R (panel X x)
lemma tang_rad (x y:Tri s)(p:delta x y≤R.L.val): delta (tang R x) (tang R y) ≤1:= delta_le.mpr fun i=> radial R.geom 0 (x i) (y i) ((Grid.delta_at ..).trans p)
lemma radial_foot (u v:X.Hcols)(p:delta u.2 v.2≤R.L.val)(q:u.1=v.1): (shape X R).span (own X R u) (own X R v) ≤1:=by refine max_le ?_ (tang_rad R _ _ p); rw [q,d_id]; omega -- tune q dsimp
lemma dispatch {x y:Site s}(p:R.L.val≤ b.full.val)(v:separation x y≤ R.L.val) : (shape X R).span (plan X R x) (plan X R y) ≤1:= max_le (radial X.size_eq (amark ..) _ _ ((delta_at x y 0).trans (v.trans p))) (tang_rad R _ _ ((Wealth.tail_sep ..).trans v)) -- tune
lemma outcast (x i:X.Index)(v:Tri R.period) : (shape X R).span (x,v) (i,v) =delta1 X.Q x i:=by unfold shape; simp
lemma adjacent (x:X.Index) (v:Tri R.period): (shape X R).span (x,v) (x+1,v)≤1:= by rw [outcast,d_sym]; simpa using delta_nat x 1
-- bay in our torus connected and PL growth
lemma morph {S T :Type}[Fintype S][DecidableEq S][Fintype T][DecidableEq T](F:Branch.Field S)(A:Finset S)(p:Grove F A)(G:Branch.Field T) (f:S→T)(h:∀ i∈A,∀ j∈A,F.span i j≤1→G.span (f i) (f j)≤1): Grove G (A.image f):=by
 induction p with|single x=> rw [image_singleton]; exact Grove.single _| @join A x y g hy t ih=> rw [image_insert]; exact Grove.join (ih (fun i w j t=>h i (mem_insert_of_mem w) j (mem_insert_of_mem t))) (mem_image_of_mem _ hy) (h x (mem_insert_self ..) y (mem_insert_of_mem hy) t)
lemma proj_g {S:Seal (Site s)}(v:Grove (Grid.field 4 s) S) : Grove (Grid.field 3 s) (S.image (fun x=>Fin.tail x)):= morph _ _ v _ _ fun i _ j _ b=> (Wealth.tail_sep ..).trans b
lemma crowd (V:Seal X.Hcols)(p:Turf X V): Grove (shape X R) (V.image (own X R)):= morph _ _ p.1 _ _ fun i g j v h=> radial_foot X R i j (h.trans R.L.property) (p.2 i g j v)
lemma fold_g (i:X.Index)(V:Seal (Tri s))(p:Grove (Grid.field 3 s) V) : Turf X (V.image (Prod.mk i)):= ⟨morph _ _ p _ _ (fun i _ j _ h=> h), fun l u k v=> by obtain ⟨l,h,rfl⟩:= mem_image.mp u; obtain ⟨l,h,rfl⟩:= mem_image.mp v; rfl⟩ -- tune R argument drops? path.
-- bay growth =1D hist plus tang. need generic for column too (Weave cost_bay)
def const0 {s: Side} (x:Per s) : Space 1 s:= fun _=>x
@[simp] lemma const_d {s:Side} (x y:Per s) : delta (const0 x) (const0 y)=delta1 s x y:= Nat.le_antisymm (delta_le.mpr fun _=> le_rfl) (delta_at (const0 x) (const0 y) 0)
lemma univ_growth {r n:ℕ}{s: Side}(x:Space n s): (bay (Grid.field n s) x r).card ≤ (4*r+1)^n:= local_count (r:=1) (one_dvd _) _ x (by rw [mul_one]) (fun i _=> fun j=> one_dvd _) (by norm_num)
lemma capacity (i:SiteX X R)(r:ℕ) : (bay (shape X R) i r).card ≤ (4*r+1)^4:=by
 let S:=bay (Grid.field 1 X.Q) (const0 i.1) r; let T:=bay (Grid.field 3 R.period) i.2 r; let g:= fun j:SiteX X R=> (const0 j.1,j.2); have he:(bay (shape X R) i r).card≤(S×ˢ T).card:=by apply card_le_card_of_injOn g ?_ ?_; intro j t; obtain ⟨a,b⟩:= max_le_iff.mp (show (shape X R).span i j ≤ r from (bay_mem _).mp t); exact mem_product.mpr ⟨(bay_mem _).mpr ((const_d ..).le.trans a),(bay_mem _).mpr b⟩; intro j _ k _ e; exact Prod.ext (congrFun (Prod.mk.inj e).1 0) (Prod.mk.inj e).2
 apply he.trans; rw [card_product]; exact (mul_le_mul' (univ_growth (const0 i.1)) (univ_growth i.2)).trans (Eq.le (by ring))
lemma one_lower {r:ℕ}(x y: Per s)(p:delta1 s x y≤r+1):∃ z:Per s,delta1 s x z ≤ r∧ delta1 s z y≤1:=by obtain ⟨z,u,v⟩:=decrease_bay (const0 x) (const0 y) ((const_d ..).trans_le p); exact ⟨z 0,(delta_le.mp u) 0,(delta_le.mp v) 0⟩
lemma in_shape (x y: SiteX X R)(r:ℕ)(p:y∈ bay (shape X R) x (r+1)): ∃ z ∈bay (shape X R) x r,(shape X R).span z y≤1:=by
 obtain ⟨a,b⟩:= max_le_iff.mp (show (shape X R).span x y≤r+1 from (bay_mem _).mp p); obtain ⟨z,g,h⟩:=decrease_bay x.2 y.2 b; obtain ⟨f,e,t⟩:= one_lower x.1 y.1 a; exact ⟨(f,z),(bay_mem _).mpr (max_le e g),max_le t h⟩
lemma body_path (x y:SiteX X R)(r:ℕ)(p:y∈bay (shape X R) x r): Origin (shape X R) (bay (shape X R) x r) x y:=by
 induction r generalizing y with
 | zero=> obtain ⟨p,q⟩:= max_le_iff.mp (show (shape X R).span x y ≤ 0 from (bay_mem _).mp p); rw [show x=y from Prod.ext (d_equal _ _ (Nat.eq_zero_of_le_zero p)) (eq_of_delta _ _ (Nat.eq_zero_of_le_zero q))]
 | succ r ih=>
   obtain ⟨z,t,g⟩:= in_shape X R x y r p; let A:=shape X R; have he:bay A x r⊆bay A x (r+1):= fun i p=>(bay_mem _).mpr (((bay_mem _).mp p).trans (Nat.le_succ _)); exact .tail (orig_sub (ih z t) he) ⟨he t,p,g⟩
lemma body_bay (x:SiteX X R)(r:ℕ) : Grove (shape X R) (bay (shape X R) x r):= trunk ((bay_mem r (y:=x)).mpr (by rw [(shape X R).reflex]; omega)) (fun i h=> body_path X R x i r h)
-- Note mathlib multip BMI. Later column cubefiber
end YM.CF.BPress.Locale
