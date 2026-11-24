import YM.CF.BProof.Anthem.Waltz
import YM.CF.BProof.Trek.Mesh
/-! Permit realized on Script, so exact mask cancellation & reservation on the real field. -/
set_option autoImplicit false
set_option synthInstance.maxSize 24000
set_option quotPrecheck false
noncomputable section
namespace YM.CF.BProof.Payment
open Function Filter NormedSpace Finset MeasureTheory
open Cube Lattice Tenant SU Lat Dial Tulip Fock Skye Spin Branch Hearth Hero Stint Oasis Scree Palot Wick Crystal Garden Veil Trek Mark Mapping Angular Anthem
open Tape
open scoped Topology BigOperators InnerProductSpace Matrix MatrixOrder Matrix.Norms.L2Operator Classical Hearth Tape Mark
attribute [local instance] opCStarAlgebra
variable {m s o N:Side}{j:ℕ}{δ c η a b l r:ℝ}{K:Core j a b l r N}{I:Type}[Fintype I] {Y:Yard (More N)}(Q:Score Y I)
section
variable {R:ℝ}
def eyeliner (Z:Pane N)(e: Eyes (More N))(i:Y.Index): World N:= Anthem.fiddle Y i Q.S Q.f Z e
def desire (z:Pane N)(v:Y.FaceS):Plant N:= cbra (Q.SBook z v) (Score.chamber Y univ)ᶜ
variable (v:Y.FaceS)(p:Pane N)(x:Loft K δ c rateH η)(S:Trek.Blocks Y m)
abbrev LastC:= roam x.val.2.val (false,false) 1
def commuteMask(S:Support (More N))(U:Pane N)(x:World N):= (pine N).agree S U x.1.2.weather -- for actual use Warp.
structure Pick (v:Y.FaceS)(z:Pane N)(x:Loft K δ c rateH η)(ρ:ℝ)(M:Support N)(X:Stun N) : Prop where
 safe(i:Site (More N)):SealH (LastC x i)
 apart : Disjoint x.val.1.val.2 M
 slow : Slow (carried x.val.1) (hook X) ρ
 scene: view x (true,false) 0=postC X
 beam:sunny x
 stamp(i:Site N)(h:i∉M): (cbra (LastC x) x.val.1.val.2).leaf i=(desire Q z v).leaf i
 spoke(i:Y.Index)(j:I)(h:j∈ Q.M.sung Y i Q.r): (world N).agree (Q.M.floor j) (eyeWorld z (sion x) X) (eyeliner Q z (v i) i)
variable {u v' d:ℝ}{H:Herald u v'} {t:ℕ}{C:Sized t H.whole} {g: Ratio m (More N)} {f:Ratio s (More N)}(G:Trek.Lamp C g S δ p (carried x.val.1)) -- repair above knot m*B only. use carried
variable (w:Y.Glyph)

variable (L:Pad Y H C g.count.val)(z: Permit (Trek.actual Q.S Q.f p Y v w) C p g S d)(A:Sound Y H C d)(V:4≤ (s:Side).val)(W:f.count=H.whole)




include G z L A V W
lemma ticket (e:x.val.1.val.2=Pins Y g S)(k:x.val.2=(Tape.drawB (Script.HH (Trek.actual Q.S Q.f p Y v w) C g S (carried x.val.1) f) (fun p' => (Permit.HPort (Trek.actual Q.S Q.f p Y v w) C g S (carried x.val.1) f L V W G z A p').1)))(uP:C.nearM≤Q.r): Pick Q v p x u (eraseBit Y g Q.r S) (Script.XX (Trek.actual Q.S Q.f p Y v w) C g S (carried x.val.1) f):=by
 obtain ⟨u,v',g',d⟩:= Permit.readyStory L z V W G A _ k; let F:=(carried x.val.1)
 let P(i):= (z.HPort (Trek.actual Q.S Q.f p Y v w) C g S (carried x.val.1) f L V W G A i).1
 let ht(i):SealH (LastC x i):=by unfold LastC; rw [d]; exact (P i).1 _
 refine ⟨ht,e.symm ▸ pins_ne Y g Q.r S, g',v',u,?_,?_⟩ -- u shadow, pins proof
 · intros j h; let B:=Score.chamber Y univ; change (if j∈ x.val.1.val.2 then (folk N).leaf j else (Garden.broad _).leaf j)=if j∈ (Score.chamber Y univ)ᶜ then (folk N).leaf j else (Garden.broad _).leaf j
   rw [e]; by_cases p':j∈ Score.chamber Y univ
   · have hh:= (Score.darkCh ..).1 p'
     have ht:= band_pick Y _ hh; let i:=hr Y (node j)
     have hp:j∉ Pins Y g S:= fun u=> (pins ..|>.1 u).1 hh
     rw [if_neg hp,if_neg (fun u=>mem_compl.mp u p')]; apply Garden.leaf_eq; rw [Q.timbre p v i _ ht]; unfold LastC; rw [d]; exact z.erase_ok L V W G A uP j ht h -- tune
   have hu:j∈ Pins Y g S:=by by_contra H; exact h ((eraseD Y g Q.r S j (mt (Score.darkCh ..|>.mpr) p')).mpr H)
   rw [if_pos hu,if_pos (mem_compl.mpr p')]
 intro i j h; let T:=Q.M.floor j; have hp:T⊆Y.band i:= (mem_filter.mp h).2.1
 have hq(t)(t₀:t∈T):= z.continuityBudget L V W G A uP (hp t₀) (fun z=> (mem_filter.mp h).2.2 t t₀ ⟨_,z⟩)
 -- equality from Pace outside
 have hl:(pine N).agree T (carried x.val.1) p:=(pine_eq T).2 (fun j a u=> (G.outside j (hq _ a).2.2 (hq _ u).2.2).symm)
 have hx:(shoots N).agree T x.val.1.val.2 ∅:= by unfold RecN.agree shoots; rw [e]; simp only [filter_empty]; apply filter_eq_empty_iff.mpr; intro i hv hg; exact (pins Y g S i|>.1 hv).1 (codeB Y (hp hg)).1
 have hf:(curving N).agree T x.val.2.val (muses Y i Q.S Q.f p (v i)):=by
   apply (curve_rule _).2; intro a t; rw [k]; exact Tape.eq_draw (p:=P a) (q:=(nightsM Y i Q.S Q.f p (v i) a).1) (hq _ t).1
 exact (Veil.paired T).2 ⟨(Veil.paired T).2 ⟨rfl, (Veil.equalize T _ _).2 ⟨hl,hx,hf⟩⟩,(tent_eq T).2 fun i' hv=>(hq _ hv).2.1⟩
end
end YM.CF.BProof.Payment
