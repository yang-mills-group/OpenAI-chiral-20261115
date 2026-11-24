import YM.SU5.LitCurrent.Source
set_option autoImplicit false
set_option synthInstance.maxSize 28000
set_option maxHeartbeats 600000
noncomputable section
namespace YM.CF.LitCurrent
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour
open Stax Skye Jet Scroll Finset Palot Cadre Vow RG Rive Nor Hake MeasureTheory
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill
open Kennel Swell StressExchange
variable {N:Side}{X Y:SOp N}{o:Seat N}{a b c d v:ℝ}{r:ℕ}
local notation "I" => Single N
open Buffered Salt
/- All paths with first inputs pulled. marks even on second arbitrary. Supply the physical
   support via tendril and Vij pressure surrogates via groove 24. -/
section spatial
lemma cut_scope {C:Sa N}{W:Op I}
    (h:∀ i j:Single N,W i j≠0 → node i.1.1∈C ∧ node j.1.1∈C):
    cutM (modesIn N C)*W*cutM (modesIn N C)=W:=by
 ext i j; by_cases he:W i j=0
 all_goals unfold cutM; rw [Matrix.mul_diagonal,Matrix.diagonal_mul]
 · simp [he]
 obtain ⟨m,k⟩:=h i j he
 rw [if_pos (show i∈modesIn N C from (modes_at ..).mpr m),if_pos (show j∈modesIn N C from (modes_at ..).mpr k)]; simp
lemma scope_cut {C:Sa N}{W:Op I}
    (h:cutM (modesIn N C)*W*cutM (modesIn N C)=W)(i j:Single N)(v:W i j≠0):
    node i.1.1∈C ∧ node j.1.1∈C:=by
 have t:= show (cutM (modesIn N C)*W*cutM (modesIn N C)) i j≠0 from h.symm ▸ v; unfold cutM at t; rw [Matrix.mul_diagonal,Matrix.diagonal_mul] at t; split_ifs at t with m k; exact ⟨(modes_at ..).mp m,(modes_at ..).mp k⟩; all_goals simp at t
private lemma soakHalo (w t g:ℕ)(x y:Site N)(p:separation x y ≤ g)(h:t+2*g≤w): offsetMask t y⊆ offsetMask w x:=by
 intro i v; obtain ⟨z,u,l⟩:=halo_spec.mp v; rw [mem_singleton.mp u] at l; exact halo_spec.mpr ⟨_,mem_singleton_self _,(separation_triangle (node x) (node y) i).trans (Nat.le_trans (Nat.add_le_add_left l _) (by rw [Hove.ζdist]; omega))⟩
private lemma rake_warm (T:Site N→Op I)(x:Site N)(d:Axis)(r w:ℕ)
    (h:∀ y:Site N,cutM (modesIn N (offsetMask w y))*T y*cutM (modesIn N (offsetMask w y))= T y):
    let C:= cutM (modesIn N (offsetMask (w+2*r) x)); let W:=StressExchange.rake (step d) T r x; C*W*C=W:=by
 induction r with
 | zero => simpa [StressExchange.rake]
 | succ r p=>
   let C:= modesIn N (offsetMask (w+2*(r+1)) x); let U:= cutM C
   let T':=StressExchange.rake (step d) T r x; let z:=stopBeam x d r; let t:=stopBeam x d (r+1)
   have he(x':Site N)(v:separation x x' ≤ r+1):U*T x'*U=T x':=cut_scope fun i j u=> by
      have hp:=scope_cut (h x') i j u; exact ⟨soakHalo _ w (r+1) x x' v le_rfl hp.1, soakHalo _ w (r+1) x x' v le_rfl hp.2⟩
   have hp:U*T'*U=T':=cut_scope fun i j u=> by
      have hv:=scope_cut p i j u; exact ⟨Corona.halo_mono (show w+2*r≤w+2*(r+1) by omega) le_rfl hv.1, Corona.halo_mono (show w+2*r≤ w+2*(r+1) by omega) le_rfl hv.2⟩
   change U*(_+ _+_+_+T (x-(r+1) • step d))*U= T' + _ + _ + _ + _
   simp only [mul_add,add_mul]; rw [show U*T' *U=T' from hp,he (x+r • step d) (z.1.trans (Nat.le_succ _)),he (x-r • step d) (z.2.trans (Nat.le_succ _)),he (x+(r+1) • step d) t.1,he (x-(r+1) • step d) t.2]
lemma room_local (x:Site N)(r w:ℕ)(h:8*r ≤ w): cutM (modesIn N (offsetMask w x))* roomW x r*cutM (modesIn N (offsetMask w x))= roomW x r:=by
 have ht(Li:List Axis)(x:Site N):let C:=cutM (modesIn N (offsetMask (Li.length*(2*r)) x)); C*cubelet r Li houseW x*C=cubelet r Li houseW x:=by
    induction Li generalizing x with
    | nil=> apply cut_scope
            intro i j t; change (houseW x) i j≠0 at t; have hx:j=i:= by by_contra u; exact t (Matrix.diagonal_apply_ne _ (Ne.symm u))
            subst j; have hu:i∈ inhabit x:=by by_contra u; apply t; simp [houseW,cutM,u]; -- tune indentation
            rw [show i.1.1=x from (mem_filter.mp hu).2]; exact ⟨halo_subset _ _ (mem_singleton_self _),halo_subset _ _ (mem_singleton_self _)⟩
    | cons i L h=>
       rw [List.length_cons,add_mul,one_mul]; exact rake_warm _ _ _ _ _ h
 apply cut_scope; intro i j e; have hu:= ht arcOrder x; have he:=scope_cut hu i j e; have hw:arcOrder.length*(2*r)≤w:=by change 4*(2*r) ≤ w; omega
 exact ⟨Corona.halo_mono hw le_rfl he.1, Corona.halo_mono hw le_rfl he.2⟩
end spatial

variable {P T:SOp N}{p:BudgetPoint}{K:Scree.Loom N}{t u:ℝ}{k q:ℕ}
variable (w:ℝ)(z:Checked p K t d a k q)(x:Site N)(E:Pattern P T r d a v)
include z
lemma surrogate_sector (l:ℕ)(h:p.B+2*r+12 ≤ l*p.B)(t:8*r≤p.B)(U:Fields N):
    Fock.Sector (modesIn N (grooveB l p (node x))) false (surrogate K p k w x E U):=by
 let M:=modesIn N (grooveB l p (node x))
 have hx(y:Site N)(v:inspectFoot p y⊆ tendril p r x): modesIn N (offsetMask p.B y) ⊆ M:= modes_monotone (((halo_foot p y).trans v).trans (words_fit p x l h)) -- syntax
 rw [surrogate, Pi.sub_apply,Pi.add_apply,Finset.sum_apply,sub_eq_add_neg]
 refine Fock.Sector.add (Fock.Sector.add (Fock.Sector.one.scale _) ?_) ?_ -- name
 · apply Fock.Sector.sumS; intro i v; let y:=destSite x r i; let F:=carrierHat K p k y E i; have ht:=pair_charge (modes_pass y (E.J (y,i)) z (E.moorJ (y,i)) (U.1,Classical.arbitrary _))
   change Fock.Sector M false (liftHalf w (F U.1)); rw [liftHalf,sub_eq_add_neg,← neg_one_smul ℂ]
   exact Fock.Sector.add (lift_v ht (hx y (fun x X=>mem_union_right _ (mem_biUnion.mpr ⟨i,v,X⟩)))) (((Sector.one.scale _).scale _).scale _)
 rw [←neg_one_smul ℂ]; apply Fock.Sector.scale; unfold excess; split
 · rw [sub_eq_add_neg,←neg_one_smul ℂ]; exact Sector.add (lift_v (pair_charge (room_local x r _ t)) (hx x subset_union_left)) ((Sector.one.scale _).scale _)
 exact Sector.zero _
end YM.CF.LitCurrent
