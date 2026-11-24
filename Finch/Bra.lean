import Finch.MatrixMark

set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.Swell
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet NormedSpace Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Prism Nacre Laic Tap Levier Thera Moto Oath Font Haro Spire Dial Rill Buffered StressExchange Window
variable {N:Side}{P:SOp N}{a b c d v s t:ℝ}{p:BudgetPoint}{k r:ℕ}{A:Scree.Loom N}{O:Site N}(h:Roof N b d r A)(u:0<d)
lemma commuteWind (O:Site N) (m:ℕ): Commute (tickA N) (windmill O m):=by
 unfold windmill; generalize List.ofFn _ =L; induction L generalizing O with
 | nil=> change Commute _ (millQ O); rw [millSt,touchP]; unfold cutM Tye.stock Commute SemiconjBy; rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]; apply congrArg; ext1 i; exact mul_comm ..
 | cons i L t=> exact Commute.sum_right _ (fun x=>squareSum millQ m L (moveSite (O - m • step i) i (x+1))) _ (fun i _=> t _)

lemma paySand (O:Site N)(m:ℕ)(U:Orbit N) : acts (star (barS0 N m O U)) (mateK N)=0:=by
 unfold barS0; rw [star_sub,star_smul,star_one,act_sub,act_smul,sandwichV _ (Cascade.plus_P _) (commuteWind ..) _ (tickB _),act_one,sub_self]
-- diagonal occupancy support within root. Also cutT price pm.
lemma allowsWind (O:Site N)(m:ℕ)(X:Finset (Seat N))(h: halo (24*m) {node O}⊆ X):
    cutM (modesIn N X)*windmill O m*cutM (modesIn N X)=windmill O m:=by
 let G(L:List Axis)(x:Site N):=squareSum millQ m L x
 let z:Op (Single N):=cutM (modesIn N X)
 have e(L:List Axis)(x:Site N)(p: halo (L.length*(6*m)) {node x} ⊆ X): z*G L x*z=G L x:= by
    induction L generalizing x with
    | nil=>
       change z*millQ x*z=_; unfold G squareSum; rw [millSt]; unfold z cutM Tye.stock; ext i j; rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal]; by_cases q:i=j; swap; · simp [*]
       subst j; by_cases e:place_x i=node x; swap; · simp [e];
       have g:i∈ modesIn N X:= (modes_at X i).mpr (show place_x i∈X from e.symm ▸ p (halo_subset _ _ (mem_singleton_self _)))
       simp [-modes_at,g,e]
    | cons i L t=>
       unfold G squareSum stripSum; rw [mul_sum,sum_mul]; refine sum_congr rfl fun j a=> t _ ?_
       let y:=moveSite (x-m • step i) i (j+1); have hu:separation x y≤3*m:=leap_strip x i m j (mem_range.mp a)
       refine Subset.trans ?_ p
       intro k w; obtain ⟨s,w,d⟩:=halo_spec.mp w
       apply halo_spec.mpr; rw [show s=node y from mem_singleton.mp w] at d
       refine ⟨node x,mem_singleton_self _,(separation_triangle _ (node y) _).trans ?_⟩; rw [Hove.ζdist,List.length_cons,add_mul]; omega
 apply e; simpa [List.length_ofFn,Axis, Nat.mul_assoc, ←mul_assoc 4 6 m, show 4*6=24 from rfl] using h -- test simp loop

lemma evenSub {I:Type*} [Fintype I][LinearOrder I] {T:Finset I}{X Y:FC I}(p:Sector T false X)(g:Sector T false Y): Sector T false (X-Y):=by simpa [sub_eq_add_neg] using p.add (g.scale (-1))
lemma cashSector {I:Type*} [Fintype I][LinearOrder I] (T:Finset I) (C:Op I)(h:cutM T*C*cutM T=C):Sector T false (dg C):=by
 unfold dg dyad; refine Sector.sumS _ _ fun i _=>Sector.sumS _ _ fun j _=>?_; by_cases g:C i j=0; · rw [g,zero_smul]; exact Sector.zero false -- arg?
 have hp:i∈T∧ j∈T:=by
    by_contra v; apply g; rw [← h,cutM, Matrix.mul_diagonal,Matrix.diagonal_mul]; split_ifs <;> first|tauto|simp
 exact ((Sector.up i hp.1).mul (Sector.down j hp.2)).scale _ -- order?

include h u
lemma coverLine_ink (S:SOp N)(i:Site N)(x:Site N)(X:Trunk (node x) S k a v d)(g:p.threshold≤ b)(l:k+r≤ p.B)(V:Orbit N) :
    coverLine A p x i S V=dg (markMatrix A p (node i) (co_Ψ i x S) V.1):=by
 have e:= X.travels (taxiPlus (i-x)); rw [platforms,add_sub_cancel] at e
 unfold coverLine houseK; by_cases y:V∈pingMask p (offsetMask p.B i)
 · rw [Set.indicator_of_mem y, ink_here h u e l g _ V.2 y]
 rw [Set.indicator_of_notMem y, ink_away _ y]; simp [dg,dyad]
lemma puff_uses (X:Trunk (node O) P k a v d)(g:p.threshold≤ b)(l:k+r≤ p.B)
    (J:Axis→ SOp N)(w:∀ a':Axis,Trunk (node O) (J a') k a v d)(m:ℕ)(V:Orbit N):
    acts (star (puffLine A p O J P m V)) (mateK N)=acts (star (finchWardMark A p O J P m V.1)) (mateK N) ∧ Sector (modesIn N (wardZone p O m)) false (puffLine A p O J P m V):=by
 let o:Seat N:= node O; let S:= halo p.B {o}; let F(x:Site N)(i:Axis):=markMatrix A p (node x) (co_Ψ x O (J i)) V.1; let z0:=houseK p S (barS0 N m O) V; let T:=wardZone p O m
 have e: puffLine A p O J P m V= gaugeOnlyMark A p O P V.1-z0+∑ i:Axis,(dg (F (O+gapPlus i m) i)-dg (F (O-gapPlus i m) i)) := by
    unfold puffLine highLine; rw [Pi.add_apply,Finset.sum_apply]; simp_rw [Pi.sub_apply]; refine congrArg₂ _ ?_ (sum_congr rfl fun i _=> congrArg₂ _ (coverLine_ink h u _ _ _ (w i) g l V) (coverLine_ink h u _ _ _ (w i) g l V)) -- tune simp changes houseK
    change houseK p S _ V = _-_; unfold z0 houseK gaugeOnlyMark inkCost; by_cases f:V∈pingMask p S
    · rw [Set.indicator_of_mem f,Set.indicator_of_mem f,ink_here h u X l g _ V.2 f]; rfl
    rw [Set.indicator_of_notMem f,Set.indicator_of_notMem f,ink_away _ f]; simp
 rw [e]
 have w0: acts (star z0) (mateK N)=0∧ Sector (modesIn N T) false z0:=by
    unfold z0 houseK; by_cases f:V∈pingMask p S
    · rw [Set.indicator_of_mem f]; exact ⟨paySand ..,evenSub (cashSector (modesIn N T) (windmill O m) (allowsWind O m T (Corona.halo_mono (by omega) le_rfl))) (Sector.one.scale _)⟩
    rw [Set.indicator_of_notMem f]; exact ⟨by simp only [star_zero,act_zero],Sector.zero false⟩
 constructor
 · unfold finchWardMark; rw [Pi.add_apply,Finset.sum_apply]; simp_rw [Pi.sub_apply,star_add, star_sub, star_sum, act_add, act_sum,act_sub, w0.1,sub_zero]; refine congrArg _ (sum_congr rfl fun i _=>?_); rw [star_sub,star_sub,act_sub,act_sub]; exact congrArg₂ (·-·) (bra_eq (F (O+gapPlus i m) i) (Cascade.plus_P N) (mateK N) (tickB N)) (bra_eq (F (O-gapPlus i m) i) (Cascade.plus_P N) (mateK N) (tickB N))
 have hz(i:Axis)(x:Site N)(j:separation O x≤ m) : Sector (modesIn N T) false (dg (F x i)):=by
    let H:=w i; have h':=H.travels (taxiPlus (x-O)); rw [platforms,add_sub_cancel] at h'; apply cashSector _ _ (ink_spots h u h' p _ _ ((Corona.halo_mono (show k≤ p.B+12 by omega) le_rfl).trans (zone_fit x O _ _ j)))
 exact (evenSub (Sector.one.scale _) w0.2).add (Sector.sumS _ _ fun i _=> evenSub (hz i _ (stopBeam O i m).1) (hz i _ (stopBeam O i m).2))

end YM.CF.Swell
