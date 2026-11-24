import YM.CF.Buffered.Crate
/-! # Regrouping slabs. Mass at rectangle evaluated with Batch. -/
set_option autoImplicit false
set_option synthInstance.maxSize 22000
set_option maxHeartbeats 480000
noncomputable section
namespace YM.CF.Buffered.Region
open Function Filter NormedSpace SU Lat Lattice Cube Finset Mir Mir.Trip Phase RP MeasureTheory Roost Rails Mil RG WilsonStartup Spark Nova Fock Push.SectorMeasure Ordered Cin Stripe Tile Traversed Stack Bays Saddle
open Installed (point)
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Kronecker Topology ComplexOrder Fin.NatCast
attribute [local instance] opCStarAlgebra
variable {m v p B n:Side}{δ:Axis→Side}{i:Axis}{ζ:TStem i}
variable {e x:ℝ} (K: Ticket m v B p e x) (Z: Rail δ → Badge v B)(q:Clip)(β u:ℝ)
local notation "N" => n.val
local notation "C" => Car ζ
local notation "G" => GridM v B
local notation "X" => Wet ζ v B
local notation "A" => Wide ζ v B
local notation "d" => EdgePorts ζ v B
local notation "D" => DeckIn N X X
local notation "T" => Fin n.val
namespace Saddle
variable (V:Traversed ζ δ n)
abbrev Outdoors (ζ:TStem i)(n: Side)(v B:Side):= Bays (Fin n.val) (Wide ζ v B)
local notation "O" => Outdoors ζ n v B
def rooms (V:Traversed ζ δ n)(v B:Side): Installed (Rail δ) (GridM v B) (Outdoors ζ n v B):=
 (V.click.symm.prodCongr (Equiv.refl _)).trans ((Equiv.prodAssoc _ _ _).trans (((Equiv.refl _).prodCongr (wall _ _)).trans (wall _ _)))
local notation "F" => rooms V v B
def portage (V:Traversed ζ δ n)(t:T) : C ↪ Rail δ := (point V.click t)
lemma deput (t:T)(j:C)(k:G): install _ t (install _ j k)=point F (V.loc t j) k:=by change _=point F (V.click (t,j)) k; dsimp only [point,rooms, Equiv.trans_apply,Embedding.coeFn_mk,Equiv.prodCongr_apply]; rw [show (V.click.symm.prodCongr (Equiv.refl _)) (V.click (t,j),k)=( (t,j),k) from Prod.ext (Equiv.symm_apply_apply _ _) rfl]; rfl

def curve (v B:Side)(V:Traversed ζ δ n): Batch N (Wide ζ v B) (Outdoors ζ n v B) where
 site:= fun t=> install (Wide ζ v B) t
 grade:= Rect.above (rooms V v B)
 post:= upper ζ v B
 rider := fun i j h=> Installed.apart (wall _ _) h -- implicit many
 care t y := by
    rcases y with ⟨z,y⟩; rw [show Rect.above (rooms V v B)=Installed.filled (rooms V v B) (sky v B) from rfl]; rw [show install (Wide ζ v B) t ⟨z,y⟩ = _ from deput (B:=B) V t z y]; exact (Installed.point_grade ..).trans (Installed.point_grade ..).symm
local notation "R" => curve v B V
variable (a: Fin n.val→ Bool)
def record : Many N (Film X X d A):= fun t=> printF K (Z ∘ (V.loc t)) q β u (a t)
variable (w:DeckIn n.val (Wet ζ v B) (Wet ζ v B))
local notation "λM" => Saddle.record K Z q β u V a
local notation "p₀" i:max j:max => (point F (V.loc i j))
local notation "zQ" => scatter V a w
local notation "μ" => Measure.prod (piN n.val (fluid ζ v B)) (piN n.val (fluid ζ v B))
local notation "ρ" => Rails.law δ v B

private lemma entropy : Rect.gold K q β zQ= Batch.wgt λM w:=by unfold Rect.gold Batch.wgt; rw [←Equiv.prod_comp V.click, Fintype.prod_prod_type]; refine prod_congr rfl fun i _=>?_ ; unfold Saddle.record; change (∏ j:C,_)= space _ _ _ _ _; apply prod_congr rfl; intro j _; apply congrArg; exact chaired_eval ..
private lemma linear (t:T): Batch.needle R λM w t.val= into (install A t) (Rect.Badge.affix (wall C G) (Z∘(V.loc t)) (slip (a t) (atCell w t.val))):=by unfold Batch.needle Batch.place; rw [recur_of,recur_of]; rfl
private lemma compartments (t:T): Batch.needle R λM w t.val= pal _ (Rect.Badge.paired F Z (fun i=>reel i zQ)) (univ.map (portage V t)):=by
 rw [linear]; let w':=fun j=> reel j zQ; let f(j:Rail δ):= into (point F j) ((Z j).label (w' j))
 let g j:= Rect.Badge.one (wall C G) (Z ∘ (V.loc t)) (slip (a t) (atCell w t.val)) j; let tO:=into (install A t); have he (j:C) : f (V.loc t j)=tO (g j):=by
    unfold f w' g; rw [chaired_eval V _ t j w]; exact (into_trans _ _ _ (deput V t j) ((Z (V.loc t j)).state _)).symm -- tune
 let u' := Rect.Badge.paired F Z (fun j=> reel j zQ); let o(j:C):=f (portage V t j); have ht : Pairwise (fun i j=> Commute (o i) (o j)) := fun j k h=> u' ((portage V t).injective.ne h)
 rw [← pal_map (f:=o) _ _ _ (portage V t) (show _ from u') (fun i _=> rfl)]; exact pal_trans _ _ _ o ht tO.toMonoidHom fun i _=> (he i).symm -- tune
private lemma clustering {M: Type*}[Monoid M](f:Rail δ→ M)(g:ℕ→M)(h:Pairwise (fun i j=> Commute (f i) (f j)))(b:∀ t:T, g t.val=pal f h (univ.map (portage V t))):
    pal f h univ= Stack.run g N :=by
 let S(k:ℕ):=(univ:Finset (Rail δ)).filter fun j=> (lead V j).val<k
 rw [←(show S N=univ from Finset.filter_true_of_mem (fun j _=>Fin.isLt _))]; suffices ht:∀ k≤N, pal f h (S k)=Stack.run g k from ht _ le_rfl
 intro k p; induction k with
 | zero=> simp [S,pal_empty,run_zero]
 | succ k ih=>
   let y:T:=⟨k,by omega⟩; let Q:=univ.map (portage V y); have hp(i:Rail δ): i∈Q ↔ (lead V i).val=k:=by
      simp only [Q,Finset.mem_map, mem_univ,true_and]; constructor; · rintro ⟨i,rfl⟩; have ht:= lead_loc V y i; exact congrArg Fin.val ht
      intro p; exact ⟨_, show loc V y (tail V i)=i from by rw [←show lead V i=y from Fin.ext p,V.parts]⟩
   have w : Disjoint (S k) Q := by refine Finset.disjoint_left.mpr ?_; intro i e h; have hk: (lead V i).val=k:= (hp i).1 h; exact (mem_filter.mp e).2.ne hk -- tune dependent
   rw [show S (k+1)=S k ∪ Q from ?_,pal_union _ _ _ _ w, ih (by omega),run_succ]; congr 1; exact (b y).symm
   ext i; simp [S,hp,Nat.lt_succ_iff,le_iff_lt_or_eq]
private lemma logo : Rect.logo Z F zQ= Stack.run (Batch.needle R λM w) N:= clustering (V:=V) _ _ (Rect.Badge.paired F Z _) (fun t=> compartments ..)

private lemma root_step (i:T) : Batch.root R λM w i.val=exp (∑ j:C, into (p₀ i j) (Tile.seed K (reel (V.loc i j) zQ))):=by
 unfold Batch.root Batch.place; rw [recur_of,recur_of]; unfold Saddle.record; change into _ (exp (seedP _ _ _))= _; rw [into_exp]; apply congrArg; unfold seedP; rw [map_sum]; apply sum_congr rfl; intro j _; rw [chaired_eval V a i]; exact into_trans _ _ _ (deput V i j) (Tile.seed_sector ..)
private lemma hush : exp (Rect.quiet K F zQ)= Stack.run (Batch.root R λM w) N:=by
 let f(i:Rail δ):= into (point F i) (Tile.seed K (reel i zQ)); let g:= exp ∘ f
 have p':Pairwise (fun i j=> Commute (g i) (g j)):= fun i j h=> evenc (Heat.sector_exp (sector_in (point F i) (Tile.seed_sector _ _))) (Heat.sector_exp (sector_in (point F j) (Tile.seed_sector _ _))) (Installed.apart F h) -- tune
 letI : NormedAlgebra ℚ (FC O) := NormedAlgebra.restrictScalars ℚ ℝ _
 have hp(s: Finset (Rail δ)):exp (∑ i∈s,f i)=pal g p' s:= exp_sum_of_commute s _ (fun i _ j _ h=> evenc (sector_in _ (Tile.seed_sector _ _)) (sector_in _ (Tile.seed_sector _ _)) (Installed.apart F h))
 change exp (∑ i,f i)=_; rw [hp]; refine clustering V _ _ _ fun t=> ?_; rw [←hp,root_step,sum_map]; rfl
private lemma core_one (t:T): Batch.core R λM w t.val=u • ∑ p:C,(into (point F (V.loc t p)) (pit (reel (V.loc t p) zQ)) + ∑ j:Off i, Rect.scar F (V.loc t p) zQ j.val):=by
 unfold Batch.core Batch.place; rw [recur_of,recur_of]; change into _ (u • horn (a t) _)= _; rw [into_real]; apply congrArg; unfold horn; rw [map_sum]; apply sum_congr rfl; intro p _; rw [map_add,map_sum]; refine congrArg₂ (·+·) ?_ (sum_congr rfl fun j _=> ?_)
 · rw [chaired_eval V a]; exact into_trans _ _ _ (deput V t p) (pit_sector ..)
 unfold thorn Rect.scar; rw [into_real,V.ends_tip, V.taxi, chaired_eval V a, chaired_eval V a]; exact congrArg (fun x:FC O=> tip p j • x) (Tile.join_through j.val _ _ _ _ _ _ _ (deput V t p) (deput V t (Taxi p j)))
private lemma at_eq (t:ℕ) (r:T)(g:(t:Fin N)=r): atCell w t=atCell w r.val:=by unfold atCell recur; simp only [Nat.cast_add,Nat.cast_one,Fin.cast_val_eq_self]; rw [g]
-- leg footprint in frame at t. pass r argument for t+1=n possibility
private lemma leg_out (t:ℕ) (r:T)(g:(t:Fin N)=r)(u':C)(c:Kid v B i):
 Batch.leg R λM w t true (u',c)= Real.sqrt u • (into (p₀ r u') (outgo i c (reel (V.loc r u') zQ))) := by
 unfold Batch.leg Batch.place recur; rw [g, at_eq w t r g]; change into (install A r) (Real.sqrt u • waist (a r) true (u',c) (atCell w r.val))= _; unfold waist; rw [if_pos rfl,into_real,chaired_eval V a]; exact congrArg (fun x:FC O=>Real.sqrt u • x) (into_trans _ _ _ (deput V r u') (outs_sector ..)) -- tune
private lemma leg_in (t:ℕ) (r:T)(g:(t:Fin N)=r)(u':C)(c:Kid v B i) :
 Batch.leg R λM w t false (u',c)= Real.sqrt u • (into (p₀ r u') (income i c (reel (V.loc r u') zQ))) := by
 unfold Batch.leg Batch.place recur; rw [g, at_eq w t r g]; change into (install A r) (Real.sqrt u • waist (a r) false (u',c) (atCell w r.val))= _; unfold waist; rw [if_neg (by decide: ¬ false=true),into_real,chaired_eval V a]; exact congrArg (fun x:FC O=>Real.sqrt u • x) (into_trans _ _ _ (deput V r u') (ins_sector ..))
variable (L:Landing δ)(v':0 ≤ u)
include L v'
private lemma horn_age (r:T): Batch.feet R λM w r.val=u • (∑ j:C, Rect.scar F (V.loc r j) zQ i):=by
 unfold Batch.feet; rw [Fintype.sum_prod_type,smul_sum]; apply sum_congr rfl; intro j _; unfold Rect.scar; rw [Tile.join_across (h:=Installed.apart F (next_away _ i L).symm), V.verge,V.last_tip, smul_sum, smul_sum]
 refine sum_congr rfl fun i' _=>?_ ; rw [leg_out _ _ _ _ _ V a w _ r (by simp), leg_in _ _ _ _ _ V a w _ (r+1) (by simp),Algebra.smul_mul_assoc,Algebra.mul_smul_comm,smul_smul,←sq,Real.sq_sqrt v']; unfold outer; split_ifs <;> simp [Reflect.chord,smul_comm u Complex.I] -- tune
private lemma mill : u • Rect.glow F zQ=Trotter.ends (Batch.core R λM w) (Batch.feet R λM w) N:=by
 unfold Trotter.ends; rw [←Fin.sum_univ_eq_sum_range (fun i=> (_ + _:FC O))]; -- tune
 unfold Rect.glow; rw [←Equiv.sum_comp V.click, Fintype.sum_prod_type, smul_sum]; refine sum_congr rfl fun v _=>?_ ; rw [core_one,horn_age K Z q β u V a w L v',←smul_add,←sum_add_distrib]; apply congrArg; refine sum_congr rfl fun s _=>?_; rw [show V.click (v,s)=V.loc v s from rfl, add_assoc]; apply congrArg; rw [Fintype.sum_eq_add_sum_subtype_ne (f:=fun j=> Rect.scar F (V.loc v s) zQ j) i,add_comm] -- tune
private lemma channel_read : Rect.emit K Z q β u F zQ=Batch.marked λM R (Batch.finale λM R) w:=by
 unfold Rect.emit Rect.player Batch.marked Batch.finale; rw [entropy K Z, Saddle.logo K Z,hush K Z,mill K Z q β u V a w L v']; rfl
local notation "η" => fluid ζ v B
lemma at_batch : prism δ K Z q β u= Batch.input λM R η η:=by
 rw [prism, Rect.stages K Z _ _ _ _ F]; unfold Rect.vista Batch.input; let T':= scatter (v:=v) (B:=B) V a; let U(w):= Rect.emit K Z q β u F w; have hp := Rect.emit_pays K Z q β u F
 have he:MeasurePreserving T' μ ρ:= scatter_mp ..
 rw [← he.map_eq, integral_map he.measurable.aemeasurable (he.map_eq.symm ▸ hp.meas.aestronglyMeasurable)]; exact integral_congr_ae (Eventually.of_forall fun w=> channel_read K Z q β u V a w L v')
end Saddle
end YM.CF.Buffered.Region
#print axioms YM.CF.Buffered.Region.Saddle.at_batch
