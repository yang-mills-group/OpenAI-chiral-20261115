import YM.SU5.Diva.Spiro
/-! Adaptation of Fluxion,Audition,Duet. Testing ALL clans, same enrollment.
 Two tolerance orders: take R large first. The internal evaluation estimate
 is on the true spin/color/momentum form, invoked on auxiliarily-chosen sequences
 (does not need a continuum limit for these volumes). -/
set_option autoImplicit false
set_option maxHeartbeats 500000
noncomputable section
namespace YM.CF.Buffered.Ballad
open Function Filter Metric Fock Finset Fir Jill Lat Lattice Laurent Next.Free Bloch Cube Sods Tulip Scroll Spire Pastry RP Branch Wilson Phase SU Rush Mir Reflect Lifted Bilinear Window Skye Emu Onyx Kea Flare Dial
open Cache Glaze
open scoped Matrix MatrixOrder Matrix.Norms.L2Operator BigOperators InnerProductSpace Topology
attribute [local instance] opCStarAlgebra
variable {R:ℕ}{B N:Side}{j:ℕ}
open Py.Rate.LocalLimit.Papal (Weaver)
open YM.CF.Lamour YM.CF.Velvet
open YM.CF.Lamour.Bridge.Celeste
namespace Twah
open Lead (Clan)
variable (A:Twah)(U:Clan)
def seatX (i:Slot)(b:Bool):Emu.Wing:= ⟨if b then dnSpin A.low else upSpin A.up,i,1⟩
def oasis (b:Bool): Cover:= if b then A.death else A.birth
def billF (i:Slot)(b:Bool):TagT:= (A.oasis b,A.seatX i b)
def chargeF (i:Slot)(b:Bool): Reader0 (Single N):= nac 0 1 1 R (A.billF i b)
lemma uncut (x:Cover)(a:Emu.Wing): hint (0:Site N) x a 1 1=basisC N x a.a a.x := by
 rw [hint,show stemF (0:Site N) x a 1 1=1 from ?_,map_one];
 · rw [show (cote (N:=N) (1:UNI Slot)).val = 1 from ?_,act_one]
   · unfold wind; rw [show natural (0:Site N)=(0:Cover) from (by ext i; simp [natural]),zero_add, show hub a (0:Site N) x=Lifted.index N x a.a a.x from (by simp [hub, Lifted.index])]; rfl
   ext i j : 1; change jump (Equiv.refl _) (fun (_:Site N × SpinIdx)=> (1:Op Slot)) i j=(1:Op (Single N)) i j; rw [jump_apply]; rcases i with ⟨i,hx⟩; rcases j with ⟨k,l⟩; simp [Matrix.one_apply,ite_and]
   
 unfold stemF
 have h(z:Site (More N))(v:Walk): travel (1:Bkg (More N)) z v=1:=by induction v generalizing z with | nil=> rfl| cons i v ih=> rw [travel, ih,mul_one]; cases i with|mk i b=> cases b; rfl; exact inv_one
 rw [h,inv_one,mul_one]
lemma in_hi (i:Slot): ton (A.chargeF (R:=R) (N:=N) i false)=gain R • create (A.upper N i):=by
 rw [chargeF,billF,nac, uncut]; dsimp only; rw [show signW (A.seatX i false)=false by simpa only [signW,seatX,Bool.false_eq_true,ite_false,decide_eq_false_iff_not,not_not] using up_half A.up]; change create (gain R • A.upper N i)= _; rw [map_smul]
lemma in_lo (i:Slot): ton (A.chargeF (R:=R) (N:=N) i true)= (-star (gain R)) • Fock.remove (A.lower N i):=by
 rw [chargeF,billF,nac, uncut]; dsimp only; rw [show signW (A.seatX i true)=true from decide_eq_true ((show dnSpin A.low∉ plusHalf from dn_half _): ¬ _), if_pos (show true=true from rfl)]; change star (create (-(gain R • _)))=_; rw [map_neg,map_smul,star_neg,star_smul,neg_smul]; rfl
lemma bouquet : A.groundWord R U N (1,1)=∑ p∈colors U, ton (A.chargeF (R:=R) p true)*ton (A.chargeF (R:=R) p false):=by
 have h:A.laps (1:Pane N)=1:=by
    rw [laps_t]; suffices F:∀(x:Site (More N))(w:Walk),travel (1:Pane N) x w=1 from F _ _; intro x w; induction w generalizing x with| nil=>rfl| cons i v t=>rw [travel,t,mul_one]; cases i with|mk i b=>cases b; rfl; exact inv_one -- block issue
 have ht: star (gain R)*gain R=(R:ℂ)^3:=by simp only [gain,Complex.star_def,Complex.conj_ofReal]; norm_cast; rw [←sq,Real.sq_sqrt (by positivity)]
 rw [groundWord,smul_sum]; apply sum_congr rfl; intro i v; rw [Finset.sum_eq_single_of_mem i v];
 · rw [show A.coil (1:Pane N) i i=1 from (by rw [coil,h,map_one]; exact Matrix.one_apply_eq _),one_smul, in_lo,in_hi,Matrix.smul_mul,Matrix.mul_smul,smul_smul,neg_mul,ht,gold]
 intro j _ p; rw [show A.coil (1:Pane N) i j=0 from (by rw [coil,h,map_one]; exact Matrix.one_apply_ne p.symm),zero_smul]
variable {I:Type*} (Y:I→ Twah)(Z:I→Clan)(L:List I)
-- order letters explicitly; no bogus claiming freely perm even beyond roots, but equality uses fixed inputs. Allows same point and same Twah.
abbrev Stamp (I:Type*):= I × Slot × Bool
def cording(u:Stamp I):= (Y u.1).billF u.2.1 u.2.2
def pulse (N:Side)(R:ℕ) (i:Stamp I):= (Y i.1).chargeF (R:=R) (N:=N) i.2.1 i.2.2
def plait (R:ℕ): Weaver:= (L.map fun x:I=> (Y x).groundWord R (Z x)).prod
def pieces (g:List I):Finset Cover:= (g.map fun x:I=> (Y x).patio).foldl (·∪·) ∅
-- easier recurse support union
abbrev paper(I:List Twah):Finset Cover:= I.foldr (fun v l=> v.patio∪l) ∅
lemma lovely(R:ℕ): Voice (plait Y Z L R) (paper (L.map Y)):= by induction L with| nil=> exact Voice.one _| cons i l h=> exact (Gemini.flourish (Y i) _).mul h
-- keep splicing evaluation in order of blocks
abbrev sayHi {I:Type*}(l:List (Stamp I))(i:I)(v:Slot):List (Stamp I):= l++[(i,v,true),(i,v,false)]
def chore (F:List (Stamp I)→ℂ) (A:List (Stamp I)):List I→ℂ
| []=> F A
| i::l=> ∑ v∈colors (Z i), chore F (sayHi A i v) l
lemma bank_chant (h:1 ≤ j)(t:Kea.Pad j N)(M:Jill.Male)(x:Wave (Single N))(p:Sea (spar j M (1:Pane N)) x)(S:List (Stamp I)):
 alleyR (mateK N) x (rollC (ton ∘ pulse Y N R) S* plait Y Z L R N (1,1))= chore Z (runes (fun a b=> rankG (lake N j M) (pulse Y N R a) (pulse Y N R b))) S L:=by
 induction L generalizing S with
 | nil=>
    change alleyR (mateK N) x (_*(1:FC (Single N)))=_; rw [mul_one]
    have ht:= (pitch M h t.1); let T:= ht.1
    let L:= pulse Y N R
    let y:= mateK N; have hv:Sea (Dofu N (field (too N) j M)) x:= coasting t M ▸ p; have Hy:=tickB N
    have hg: skyGlow y 1 x≠0:= shines T x y hv Hy
    change (inner ℂ y x)⁻¹*inner ℂ y (acts (rollC (ton ∘ L) S) x)=runes (fun a b=> rankG (lake N j M) _ _) S
    have v:= Emu.frown T Hy hv L (fun i=> nac_k (0:Site N) 1 1 _ _) S;
    unfold pRead skyGlow at v; simp_rw [quant_one,mul_one,act_one,←ht.2] at v; rw [skyGlow,quant_one,act_one] at hg; rw [show inner ℂ y _= _ from v,inv_mul_cancel_left₀ hg]
 | cons i l p=>
    -- careful p variable shadow
    let A:= rollC (ton ∘ pulse Y N R) S; let B:= plait Y Z l R N (1,1); change alleyR _ x (A*((Y i).groundWord R (Z i) N (1,1)*B))=_; rw [bouquet,sum_mul, mul_sum, map_sum]; refine sum_congr rfl fun v _=>?_ ; rw [← p];
    apply congrArg (alleyR (mateK N) x); rw [show rollC (ton ∘ pulse Y N R) (sayHi S i v)=A*(ton ((Y i).chargeF (R:=R) v true)*ton ((Y i).chargeF (R:=R) v false)) by unfold A; simp only [rollC,sayHi,List.map_append,List.prod_append,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]; rfl]; exact (mul_assoc ..).symm -- tune extra assoc
lemma jewel_bank (R:ℕ)(h:1 ≤ j)(t:Kea.Pad j N)(M:Jill.Male)(x:Wave (Single N))(p:Sea (spar j M (1:Pane N)) x):
 alleyR (mateK N) x (plait Y Z L R N (1,1))= chore Z (runes (fun a b=> rankG (lake N j M) (pulse Y N R a) (pulse Y N R b))) [] L:=by simpa [rollC] using bank_chant (R:=R) Y Z L h t M x p []
end Twah
end YM.CF.Buffered.Ballad
#print axioms YM.CF.Buffered.Ballad.Twah.jewel_bank
