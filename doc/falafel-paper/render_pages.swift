import Foundation
import PDFKit
import AppKit
let args = CommandLine.arguments
let doc = PDFDocument(url: URL(fileURLWithPath: args[1]))!
print("pages", doc.pageCount)
for i in 0..<doc.pageCount {
    let page = doc.page(at: i)!
    let b = page.bounds(for: .mediaBox)
    let scale: CGFloat = 1.6
    let img = NSImage(size: NSSize(width: b.width*scale, height: b.height*scale))
    img.lockFocus()
    NSColor.white.set(); NSRect(x: 0, y: 0, width: b.width*scale, height: b.height*scale).fill()
    let ctx = NSGraphicsContext.current!.cgContext
    ctx.scaleBy(x: scale, y: scale)
    page.draw(with: .mediaBox, to: ctx)
    img.unlockFocus()
    let rep = NSBitmapImageRep(data: img.tiffRepresentation!)!
    try! rep.representation(using: .png, properties: [:])!.write(to: URL(fileURLWithPath: "\(args[2])/p\(i+1).png"))
}
