import YM.CF.Scion.Fry
set_option autoImplicit false
set_option synthInstance.maxSize 20000
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Scion
open Function Filter Metric NormedSpace Finset Fock Lattice Wilson Laurent Lat Rush SU Drapes Fir Peaks Dial Paige Brace Vault Tulip Tenant Phase Broc Scroll Thera Branch Laic Cube Relation
open scoped Matrix.Norms.L2Operator Matrix Topology ContDiff MatrixOrder BigOperators InnerProductSpace Kronecker
attribute [local instance] opCStarAlgebra
open Scree Pastry Stilo Urn Palot Hake
variable {ι A n M: Type*}[LinearOrder n][Fintype n][LinearOrder M][Fintype M]
lemma Reached (P:List ι)(Z:Set ι)(V:Set n)(h:Fit Z P)(L:ι→n→ℂ)(Q:ι→ι→ℂ)(p:∀ i∈Z,∀ j, L i j≠0→j∈V): Pitch put V P.length (taskC (lank L) (Stilo.price Q n) P):=by
 classical
 induction hp:P.length using Nat.strong_induction_on generalizing P with
 | h a ih=> cases P with
            | nil=> exact hp ▸ zeroW _
            | cons i F=>
                rw [task_one]; have hx := h i (List.mem_cons_self ..); have hu: Fit Z F:= fun j p=>h j (List.mem_cons_of_mem i p); have he0:F.length+1=a:=hp; have he: Pitch put V 1 (lank L i):=by
                   unfold lank; apply Pitch.sum; intro j _; by_cases g:L i j=0; rw [g,zero_smul]; exact Pitch.null
                   exact Pitch.stam _ (oneW (F:=put) (p i hx j g))
                apply Pitch.add; · rw [←he0,add_comm]; exact he.mu (ih _ (by omega) _ hu rfl)
                apply Pitch.listS; intro j g; have hf:= hu; let T:= ih j.back.length (by have h:= picks_mem (w:=j) g; omega) j.back (fun i l=>hf i ((pick_wear F g).2 l)) rfl; have hb:=T.grade (show Nat.ModEq 2 j.back.length a from by unfold Nat.ModEq; have h:= picks_mem g; omega)
                unfold Stilo.price; split_ifs; · rw [←neg_smul,Algebra.smul_mul_assoc,one_mul]; exact Pitch.stam _ hb
                rw [Algebra.smul_mul_assoc,one_mul]; exact Pitch.stam _ hb
-- single-view kernels
structure Weave (n M:Type*)[LinearOrder n][Fintype n][LinearOrder M][Fintype M] where
 seats: Twig n→ LeanV M→ℂ
 pals:Twig n→ Twig n→ℂ
 ward:KindX pals
variable {X Y:FC (LeanV n)}{U V:FC n}(W W':Weave n M)
def issue := dimeF W.pals W.seats W.ward
def cue(P:List (LeanV n))(L:List (Oboe n)):= P.map (twigExt: _ ↪ Twig n) ++ L.map (twigCab: _ ↪ Twig n)
lemma ring_u(P:List (LeanV n))(T:List (Oboe n)): issue W (rollC put P) (rollC bell T)=taskC (lank W.seats) (Stilo.price W.pals (LeanV M)) (cue P T):=(pet_r W.pals W.seats _ _ W.ward.1 W.ward.2 P T).symm
abbrev lipV(S:Set (Twig n)):= (twigExt)⁻¹' S
abbrev lipF(S:Set (Twig n)):= (twigCab)⁻¹' S
lemma cueFit {P:List (LeanV n)}{T:List (Oboe n)}{S:Set (Twig n)}(v:Fit (lipV S) P)(h:Fit (lipF S) T):Fit S (cue P T):=by
 intro i u; rcases List.mem_append.mp u with l|l<;> obtain ⟨x,k,rfl⟩:=List.mem_map.mp l; exact v _ k; exact h _ k
lemma lofty {a b:ℕ} {S:Set (Twig n)} {R:Set (LeanV M)}(p: Pitch put (lipV S) a X) (g:Pitch bell (lipF S) b U)(h:∀ i∈S,∀ j,W.seats i j≠0→j∈R): Pitch put R (a+b) (issue W X U):=by
 induction p with
 | term i l t=>
    induction g with
    | term j f y=>
       rw [ring_u]; have hp:= Reached _ _ R (cueFit t y) W.seats W.pals h; exact hp.grade (by simpa [cue] using l.add f)
    | null=> rw [map_zero]; exact Pitch.null
    | add _ _ s t=> rw [map_add]; exact Pitch.add s t
    | stam w r s=> rw [map_smul]; exact Pitch.stam w s
 | null=> rw [map_zero,LinearMap.zero_apply]; exact Pitch.null
 | add _ _ i t=> rw [map_add,LinearMap.add_apply]; exact Pitch.add i t
 | stam w _ t=> rw [map_smul,LinearMap.smul_apply]; exact Pitch.stam w t
lemma paid_u {S:Set (Twig n)}{b d:ℕ}(p:Pitch put (lipV S) b X)(v:Pitch bell (lipF S) d U) (h:∀ i∈S,W.seats i=W'.seats i)(H:∀ i∈S,∀ j∈S,W.pals i j=W'.pals i j): issue W X U=issue W' X U:=by
 induction p with
 | term i l t=>
    induction v with
    | term j d x=>
       rw [ring_u, ring_u]
       have hv(Z:List (Twig n))(u:Fit S Z):taskC (lank W.seats) (Stilo.price W.pals (LeanV M)) Z=taskC (lank W'.seats) (Stilo.price W'.pals (LeanV M)) Z:=by
         suffices L:∀ (T:List (Twig n)), Fit S T→∀ k:ℕ,ticketB (lank W.seats) (Stilo.price W.pals (LeanV M)) k T=ticketB (lank W'.seats) (Stilo.price W'.pals (LeanV M)) k T from L Z u _ -- tune
         intro T hu k; induction k generalizing T with
         | zero=> rfl
         | succ k ih=>
          cases T with
          | nil=>rfl
          | cons i L=>
           have hi:= hu i (List.mem_cons_self ..); have hl:Fit S L:=fun j e=> hu j (List.mem_cons_of_mem i e); rw [ticketB,ticketB,show lank W.seats i=lank W'.seats i from ?A,ih L hl]
           case A=> unfold lank; rw [h _ hi] -- tune
           congr 2; apply List.map_congr_left; intro j p; obtain ⟨x,t⟩:=pick_wear L p; simp_rw [Stilo.price,H _ hi _ (hl _ x),ih _ (fun i e=> hl i (t e))]
       exact hv _ (cueFit t x) -- tune indentation
    | null=> simp
    | add _ _ s t=>simp [s,t]
    | stam w _ s=>simp [s]
 | null=> simp
 | add _ _ s t=>simp [s,t]
 | stam w _ s=>simp [s]
end YM.CF.Scion
