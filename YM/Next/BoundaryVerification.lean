import YM.Next.BOUNDARY.Assembly
namespace YM.Next.BoundaryVerification
def Target : Prop := YM.Next.BOUNDARY.Producers → YM.Bid.Miles → YM.Bid.Seats → YM.Spec.CLOSED
theorem checked : Target := YM.Next.BOUNDARY.consequence
end YM.Next.BoundaryVerification
