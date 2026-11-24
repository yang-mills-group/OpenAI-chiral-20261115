import YM.CF.Buffered.TileM
/-! # The rectangles for replicated tile pressure. -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option linter.unusedSectionVars false
set_option maxHeartbeats 410000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Gloss Scroll Push.SectorMeasure Ordered Cin Stripe Tile
open Installed (point)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder
attribute [local instance] opCStarAlgebra
variable {m v p B:Side}{δ:Axis→Side}
variable {P T I J:Type*}
section chain
variable [Monoid T][DecidableEq P] (f:P→T)(u:Pairwise (fun i j=> Commute (f i) (f j)))(N:Finset P)
-- global pairwise wrapper for use when rewriting
-- codomain noncommuting monoid. Also proof of continuity will use fixed order only
def pal (f:P→T)(u:Pairwise (fun i j=> Commute (f i) (f j)))(H: Finset P) := Finset.noncommProd H f (fun _ _ _ _ h=>u h)
lemma pal_insert {i:P} (h:i∉N): pal f u (insert i N)=f i*pal f u N:= noncommProd_insert_of_notMem _ _ _ _ h
lemma pal_empty : pal f u ∅=1:=rfl
lemma pal_union (S:Finset P)(h: Disjoint N S): pal f u (N∪S)=pal f u N*pal f u S:= noncommProd_union_of_disjoint h _ _
lemma pal_congr (g:P→T)(v:Pairwise (fun i j=> Commute (g i) (g j)))(p:∀ i∈ N,f i=g i): pal f u N=pal g v N:= noncommProd_congr rfl p _
lemma pal_map {Q:Type*}(g:Q→T)(h:P ↪ Q)(v:Pairwise (fun i j=>Commute (g i) (g j)))(p:∀ i∈N,f i=g (h i)): pal f u N=pal g v (N.map h):=by
 classical
 induction N using Finset.induction_on with
 | empty=> rw [map_empty,pal_empty,pal_empty]
 | insert i S ht ih=> rw [Finset.map_insert,pal_insert _ _ S ht, pal_insert _ _ _ (by simp [ht]),p _ (mem_insert_self _ _), ih (fun j v=> p j (mem_insert_of_mem v))]
lemma pal_trans {T':Type*}[Monoid T'](g:P→ T')(v:Pairwise (fun i j=> Commute (g i) (g j)))(h:T→*T') (p:∀ i∈ N,h (f i)=g i): h (pal f u N)= pal g v N:=by unfold pal; rw [Finset.map_noncommProd]; exact noncommProd_congr rfl p _
lemma pal_list (L : List P)(p:L.toFinset=N)(h:L.Nodup): pal f u N=(L.map f).prod:= p ▸ noncommProd_toFinset _ _ _ h
end chain
local notation "A" => GridM v B
local notation "E" => Locale v B
local notation "N" => Rail δ
local notation "R" => Rails δ v B
local notation "M" => Bays (Rail δ) (GridM v B)
/-- single tile mark. Varies independently of Ticket. `Badge.one`. -/
structure Badge (v B:Side) where
 label : Locale v B→ FC (GridM v B)
 env: Envelope label
 state (x): Sector univ false (label x)
instance : One (Badge v B):=⟨⟨fun _=>1,Girt.rite_c _,fun _=> Sector.one⟩⟩

variable {e x:ℝ} (K: Ticket m v B p e x) (Z:Rail δ→Badge v B) (q:Clip) (β u:ℝ)
namespace Rect
variable [LinearOrder I][Fintype I] [LinearOrder J][Fintype J]
-- finite product bulletin
namespace Badge
variable {Z} [Fintype P] [DecidableEq P] (L:Installed P (GridM v B) I)(Y:P→Badge v B) (w:P→Locale v B)
def one (r:P): FC I:= into (point L r) ((Y r).label (w r))
lemma paired : Pairwise (fun i j=> Commute (one L Y w i) (one L Y w j)) := fun i j h=> evenc (sector_in _ ((Y i).state (w i))) (sector_in _ ((Y j).state (w j))) (Installed.apart L h) -- tune implicit
-- convenient Finset aligned single mark
noncomputable def affix := pal (one L Y w) (paired L Y w) univ
lemma affix_state : Sector univ false (affix L Y w):= by unfold affix pal; exact Finset.noncommProd_induction _ _ _ _ (fun _ _ p q=> p.mul q) Sector.one (fun i _=>uninstall (point L i) ((Y i).state _))
lemma equiv (a:I↪J)(F:Installed P (GridM v B) J)(h:∀ i z,a (point L i z)=point F i z)(y:Finset P):into a (pal _ (paired L Y w) y) = pal _ (paired F Y w) y:= pal_trans _ _ _ _ _ (into a).toMonoidHom (fun i _=> into_trans _ _ _ (h _) ((Y i).state _)) -- tune infer P
lemma affix_env {X:Type*}[MeasurableSpace X](w:P→ X→Locale v B)(e:∀ i,Measurable (w i)): Envelope (fun x:X=> affix L Y (fun i=>w i x)):=by
 suffices h:∀ y:Finset P, Envelope (fun x:X=> pal _ (paired L Y (fun i=>w i x)) y) from h _
 intro Q; induction Q using Finset.induction_on with
 | empty=> exact Girt.rite_c _
 | insert i t p ih=> simp_rw [pal_insert _ _ _ p]; refine env_mult (f:=fun x:X=> one L Y (fun i=>w i x) i) ?_ ih; exact Girt.pole_w _ _ (into_cont _) (Env.along (g:=w i) (Y i).env (e i))
end Badge

variable (F: Installed (Rail δ) (GridM v B) I)
local notation "δρ" => Rails.law δ v B
local notation "Zs" r => point F r

def scar (F: Installed (Rail δ) (GridM v B) I)(r: Rail δ)(z: R)(i:Axis) := chordF r i • joinF i (point F r) (point F (Region.next i r)) (reel r z,reel (Region.next i r) z)
def glow (z: R) := ∑ r:N, (into (Zs r) (Tile.pit (reel r z)) + ∑ i:Axis, scar F r z i)
def quiet (z:R): FC I := ∑ r:N, into (Zs r) (Tile.seed K (reel r z))
def logo (z:R): FC I := Badge.affix F Z (fun i=> reel i z)
def gold (z:R): ℂ := ∏ r:N,K.deck q β (reel r z)
def above : Finset I:= Installed.filled F (Tile.sky v B)
def player (z:R): FC I:= logo Z F z * exp (u • glow F z) * exp (Rect.quiet K F z)
def emit (z:R): ℂ:= gold K q β z * (player K Z u F z) (above F) (above F)
def vista := ∫ z:R, Rect.emit K Z q β u F z∂δρ
lemma glow_continuous : Continuous (glow F):= continuous_finsetSum _ fun i _=> ((into_cont _).comp (pit_cont.comp (reel_cont i))).add (continuous_finsetSum _ (fun j _=> ((join_cont j _ _).comp ((reel_cont i).prodMk (reel_cont (Region.next j i)))).const_smul (chordF i j))) -- tune
lemma emit_pays : Envelope (emit K Z q β u F):= by
 letI : NormedAlgebra ℚ (FC I):= NormedAlgebra.restrictScalars ℚ ℝ _
 have hp : Envelope (glow F):= Env.compact (glow_continuous F)
 have hu : Envelope (quiet K F):= Env.total _ (fun i=> Girt.pole_w _ (into _) (into_cont _) (Env.along (g:=reel i) (Tile.seed_paid K) (reel_cont i).measurable)) -- tune
 refine env_mult (Stack.product_env _ _ (fun r _=> Env.along (g:=reel r) (K.deck_ok ..) (reel_cont r).measurable)) (Girt.pole_w _ (fun P:FC I=>P (above F) (above F)) (continuous_id.matrix_elem _ _) (env_mult (env_mult (Badge.affix_env F Z _ (fun i=>(reel_cont i).measurable)) (Girt.pole_w (glow F) (fun x:FC I=> exp (u • x)) (exp_continuous (𝔸:=FC I)|>.comp (continuous_id.const_smul u)) hp)) (Girt.pole_w _ _ (exp_continuous (𝔸:=FC I)) hu)))
lemma acts_point (a:I↪J) (E':Installed N A J) (h:∀ i j,a (point F i j)= point E' i j) (z:R): into a (player K Z u F z)= player K Z u E' z:=by
 have hP : into a (glow F z)= glow E' z:=by
    unfold glow scar; simp_rw [map_sum,map_add,map_sum,into_real]; apply sum_congr rfl; intro i _; apply congrArg₂ (·+·); · exact into_trans _ _ _ (h _) (pit_sector ..)
    exact sum_congr rfl fun j _=> congrArg (fun w:FC J=> chordF i j • w) (join_through j _ _ _ _ _ _ _ (h _) (h _)) -- tune
 have hR : into a (quiet K F z)=quiet K E' z:= by unfold quiet; rw [map_sum]; apply sum_congr rfl; intro j _; exact into_trans _ _ _ (h _) (Tile.seed_sector ..)
 unfold player; rw [map_mul,map_mul,into_exp,into_exp,into_real,hP,hR]; rw [show into a (logo Z F z) =logo Z E' z from Badge.equiv F Z _ a E' h univ]
lemma changes (E':Installed N A J) : emit K Z q β u F= emit K Z q β u E':=by
 let e:= F.symm.trans E'; have he(i:N)(v:A): e.toEmbedding (point F i v)=point E' i v:=by simp only [Cin.Installed.point, Equiv.toEmbedding_apply,Function.Embedding.coeFn_mk,e,Equiv.trans_apply,Equiv.symm_apply_apply]
 funext v; unfold emit; rw [← acts_point K Z _ F _ E' he]; symm; apply congrArg; apply into_state; intro i; obtain ⟨⟨z,v⟩,rfl⟩:= F.surjective i; change e.toEmbedding (point F z v)∈_↔ _; rw [he]; exact (Installed.point_grade ..).trans (Installed.point_grade ..).symm -- tunes
lemma stages (E':Installed N A J) : vista K Z q β u F=vista K Z q β u E':=by unfold vista; rw [changes K Z _ _ _ F E']
end Rect

def prism (δ:Axis→Side)(b:Ticket m v B p e x)(F: Rail δ→ Badge v B)(q: Clip)(β u:ℝ):ℂ:= Rect.vista b F q β u (Bays.wall _ _)
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Rect.changes
