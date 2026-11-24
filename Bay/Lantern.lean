import Bay.Frond
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 3000
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.CF.Bay
open Function Filter Topology NormedSpace Lattice Wilson Fock Pastry Scree Sault Sour Stax Skye Jet Scroll Finset Palot Cadre Vow
open RG MeasureTheory Rue
open Metric Drapes Tulip Lat Branch Cube Tenant
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator InnerProductSpace BigOperators Topology Classical
attribute [local instance] opCStarAlgebra
open Rush SU Tap Levier Thera Oath Font Spire Dial Rill
open Kennel Swell


open StressExchange
open Buffered (modesIn)
variable {N:Side}

/-- Bra mate equivalence *and* mode support for use among separated sources. -/
structure Accompanies (S:footprint N)(c:ℝ)(f:Stencil N)(g:phy N) :Prop where
 pay: Fits S c f
 lives(x): Sector (modesIn N S) false (g x)
 mate(x:Orbit N): acts (star (g x)) (mateK N)=acts (star (f x.1)) (mateK N)
namespace Accompanies
variable {S T:footprint N} {c d:ℝ}{f h:Stencil N}{g j:phy N}
lemma enlarge (p:Accompanies S c f g)(r:S⊆T) : Accompanies T c f g:=
 ⟨p.pay.enlarge r,fun x=>lift_v (p.lives x) (Buffered.modes_monotone r),p.mate⟩
lemma arc(p: Accompanies S c f g)(q:Accompanies S d h j): Accompanies S (c+d) (f+h) (g+j):=
 ⟨p.pay.plus q.pay, fun x=>(p.lives x).add (q.lives x), fun x=> by simp only [Pi.add_apply,star_add,act_add,p.mate,q.mate]⟩
lemma scalar(p: Accompanies S c f g)(u:ℂ): Accompanies S (‖u‖*c) (u • f) (u • g):=
 ⟨p.pay.scalar u, fun x=>(p.lives x).scale _, fun x=> by simp only [Pi.smul_apply,star_smul,act_smul,p.mate]⟩
lemma subr(p: Accompanies S c f g)(q:Accompanies S d h j): Accompanies S (c+d) (f-h) (g-j):=by simpa [sub_eq_add_neg] using p.arc (q.scalar (-1))

lemma zeroR: Accompanies S 0 0 0:=⟨Fits.zeroR,fun _=>Sector.zero _,fun _=>rfl⟩
lemma fin {ι:Type*}(U:Finset ι)(f:ι→Stencil N)(g:ι→phy N)(a:ι→ℝ)(h:∀i∈U,Accompanies S (a i) (f i) (g i)):Accompanies S (∑i∈U,a i) (∑i∈U,f i) (∑ i∈U,g i):=by
 induction U using Finset.induction_on with
 | empty=>rw [sum_empty,sum_empty,sum_empty];exact zeroR
 | @insert i U e ih=>rw [sum_insert e,sum_insert e,sum_insert e];exact (h i (mem_insert_self ..)).arc (ih fun j h'=>h _ (mem_insert_of_mem h'))
end Accompanies
local notation "IΩ" => Single N
lemma windCo (x:Site N)(m:ℕ): Commute (tickA N) (windmill x m):=by
 suffices h: ∀ l:List Axis,∀ x:Site N,Commute (tickA N) (squareSum millQ m l x) from h _ _
 intro l; induction l with
 | nil=> intro x;rw [squareSum,millSt,touchP]; unfold Commute SemiconjBy Tye.stock cutM;rw [Matrix.diagonal_mul_diagonal,Matrix.diagonal_mul_diagonal];congr 1;ext i;exact mul_comm _ _
 | cons a l ih=> intro x; rw [squareSum, stripSum]; exact Commute.sum_right _ _ _ (fun _ _=> ih _)

lemma millSpan (x:Site N)(m:ℕ):
 sparHere (windmill x m) (modesIn N (roost (24*m) (node x))):=by
 let S:=roost (24*m) (node x)
 have ht:∀ l:List Axis,∀ y:Site N, separation x y+3*(m*l.length)≤12*m → sparHere (squareSum millQ m l y) (modesIn N S):=by
   intro l; induction l with
   | nil=>
     intro y r; simp only [List.length_nil,mul_zero,add_zero] at r;rw [squareSum,millSt]
     have g: node y ∈ S:=by apply halo_spec.mpr;refine ⟨node x,mem_singleton_self _,?_⟩;rw [Hove.ζdist];omega
     intro i j h; by_cases e:i=j; swap; · exact (h (Matrix.diagonal_apply_ne _ e)).elim
     subst j;unfold Tye.stock at h; rw [Matrix.diagonal_apply_eq] at h
     have v: place_x i = node y:= by contrapose! h;exact if_neg h
     have u:= modes_ch (i:=i) |>.mpr (show node i.1.1∈S from (show place_x i∈S from v.symm ▸ g))
     exact ⟨u,u⟩

   | cons a l ih=>
     intro y r; rw [List.length_cons,Nat.mul_add,mul_one,mul_add] at r;rw [squareSum,stripSum]; intro i j h
     rw [Matrix.sum_apply] at h
     obtain ⟨b,d,v⟩:∃ b∈range (2*m), (squareSum millQ m l (moveSite (y - m • step a) a (b+1))) i j≠0:=by by_contra! G; exact h (sum_eq_zero G)
     apply ih _ _ _ _ v
     have h:= (separation_triangle x y _).trans (Nat.add_le_add (Nat.le_refl (separation x y)) (leap_strip y a m b (mem_range.mp d)));omega
 exact ht _ _ (by rw [separation_self,List.length_ofFn]; simp;omega)

variable {p:BudgetPoint}{K:Scree.Loom N}{o:Site N}{m k:ℕ}{a c d:ℝ}
 -- remove

def blankS (K:Scree.Loom N)(p:BudgetPoint)(o:Site N)(X:SOp N):Stencil N:=glint (bayonet K p (node o) X)
def toothAt (K:Scree.Loom N)(p:BudgetPoint)(x:Site N)(V:SOp N):Stencil N:=emMark (bayonet K p (node x) V)
def tooth (K:Scree.Loom N)(p:BudgetPoint)(o x:Site N)(J:SOp N):Stencil N:= toothAt K p x (co_Ψ x o J)
def toothSum (K:Scree.Loom N)(p:BudgetPoint)(o:Site N)(J:Axis→ SOp N)(m:ℕ):Stencil N:=∑ i:Axis, (tooth K p o (o+gapPlus i m) (J i) - tooth K p o (o-gapPlus i m) (J i))
def pressY (K:Scree.Loom N)(p:BudgetPoint)(o:Site N)(J:Axis→ SOp N)(X:SOp N)(m:ℕ):Stencil N:=
 blankS K p o X + toothSum K p o J m
-- first pose toothAt x. true J+y shift even with masks.
lemma barKill (x : Orbit N) :
 acts (star (barS0 N m o x)) (mateK N) = 0:= by
 have g:IsStarProjection (tickA N):=touchP N ▸ cutM_idp _
 unfold barS0
 rw[star_sub,act_sub,sandwichV _ g (windCo o m) _ (tickB N),star_smul,star_one,act_smul,act_one,sub_self]

abbrev hollowDg (K:Scree.Loom N)(p:BudgetPoint)(x:Site N)(V:SOp N):phy N:= houseK p (offsetMask p.B x) (firePlate K V)
variable {x:Site N}{V:SOp N}
lemma atomDyed (H:Clearance p K k d)(G:BoxPay V (node x) k c d) :
 Accompanies (areaMark p (node x)) (2*c) (toothAt K p x V) (hollowDg K p x V):=by
 let A:= saleAwning H G
 have u(y:Orbit N):hollowDg K p x V y=dg (bayonet K p (node x) V y.1):=by
    unfold hollowDg houseK
    by_cases h:y∈ pingMask p (offsetMask p.B x)
    · rw [Set.indicator_of_mem h,bay_tick H G (x:=y) h]
    rw [Set.indicator_of_notMem h,bay_nil (p:=p) (o:=node x) h];simp [dg,dyad]
 refine ⟨em_fit A H.priceLen,fun y=>?_,fun y=>?_⟩
 · rw [u]; exact lift_v (dgLives (A.light _)) (Buffered.modes_monotone (roost_expand (H.priceLen.trans (Nat.le_add_left ..))))
 rw [u]; exact bra_eq _ (show IsStarProjection (tickA N) by rw [touchP];exact cutM_idp _) _ (tickB _)

def haloBar (_p:BudgetPoint)(o:Site N)(m:ℕ)(b:Bool):phy N:= if b then barS0 N m o else 0
def gauze (K:Scree.Loom N)(p:BudgetPoint)(o:Site N)(m:ℕ)(X:SOp N)(b:Bool):phy N:= houseK p (offsetMask p.B o) (blazePlate K X-haloBar p o m b)

lemma shadeRead {X:SOp N} (m:ℕ)(H:Clearance p K k d)(G:BoxPay X (node o) k c d)(r:24*m≤p.B)(b:Bool) :
 Accompanies (areaMark p (node o)) c (blankS K p o X) (gauze K p o m X b):=by
 refine ⟨glint_fit (saleAwning H G),fun y=>?_, fun y=>?_⟩
 · unfold gauze houseK
   by_cases v:y∈pingMask p (offsetMask p.B o)
   · rw [Set.indicator_of_mem v, Pi.sub_apply,sub_eq_add_neg]
     refine ((Sector.one).scale (Matrix.trace (X (profile (K y))))).add (minus_sec ?_)
     cases b
     · exact Sector.zero _
     unfold haloBar;rw [if_pos rfl,barS0,sub_eq_add_neg]
     exact (lift_v (dgLives (millSpan _ _)) (Buffered.modes_monotone (roost_expand (r.trans (Nat.le_add_left ..))))).add (minus_sec ((Sector.one).scale _))
   rw [Set.indicator_of_notMem v];exact Sector.zero _
 unfold gauze blankS houseK glint
 by_cases v:y∈pingMask p (offsetMask p.B o)

 · have hj:acts (star (haloBar p o m b y)) (mateK N)=0:=by
     cases b
     · change acts (star (0:FC IΩ)) _=_;rw [star_zero,act_zero]
     exact barKill y
   rw [Set.indicator_of_mem v,bay_tick H G (x:=y) v,Pi.sub_apply,star_sub,act_sub,hj,sub_zero]
 rw [Set.indicator_of_notMem v,bay_nil (p:=p) (o:=node o) v,Matrix.trace_zero,zero_smul]

abbrev toothCost (c:ℝ):ℝ:=2*(quota^2*c)
abbrev areaY (p:BudgetPoint)(o:Seat N)(m:ℕ):=roost ((12+p.B)+2*m) o
lemma areaFits (p:BudgetPoint)(o x:Site N)(m:ℕ)(k:separation o x≤ m) : areaMark p (node x)⊆areaY p (node o) m := by
 apply Subset.trans _ (chainR (le_refl ((12+p.B)+2*m)))
 exact Corona.halo_mono le_rfl (Finset.singleton_subset_iff.mpr (halo_spec.mpr ⟨node o,mem_singleton_self _, by rw [Hove.ζdist]; omega⟩))

lemma toothReceipt (x:Site N)(H:Clearance p K k d)(G:Trunk (node o) V k a c d)(e:0≤a):
 Accompanies (areaMark p (node x)) (toothCost c) (tooth K p o x V) (coverLine K p o x V):=by
 have h:=boxCargo (taxiPlus (x-o)) G
 rw [platforms,add_sub_cancel] at h
 exact atomDyed H (boxSeal h e)
variable {J:Axis→ SOp N}{X:SOp N}
lemma sumFits (H:Clearance p K k d)(G:∀i,Trunk (node o) (J i) k a c d)(e:0≤a) :
 Accompanies (areaY p (node o) m) (8*toothCost c) (toothSum K p o J m) (highLine K p o J m):=by
 let D:=toothCost c
 let h(i)(x:Site N)(w:separation o x≤ m):= (toothReceipt x H (G i) e).enlarge (areaFits p o x m w)

 rw [show 8*toothCost c=∑_i:Axis,(D+D) from by simp [D]; ring]
 exact Accompanies.fin univ _ _ _ (fun i _=> (h i _ (stopBeam o i m).1).subr (h i _ (stopBeam o i m).2))
abbrev costY (c:ℝ):= c+8*toothCost c
theorem baked (H:Clearance p K k d)(G:∀i,Trunk (node o) (J i) k a c d)(A:Trunk (node o) X k a c d) (r:24*m≤p.B)(e:0≤a) :
 Accompanies (areaY p (node o) m) (costY c) (pressY K p o J X m) (puffLine K p o J X m):=by
 exact ((shadeRead m H (boxSeal A e) r true).enlarge (roost_expand (le_add_of_nonneg_right (Nat.zero_le (2*m))))).arc (sumFits H G e)
end YM.CF.Bay

#print axioms YM.CF.Bay.baked
