-- ===== Key System (must pass before the script runs) =====
local function __y2k_keygate()
-- ============================================================================
--  Y2k key provider  (drop-in replacement for the Junkie SDK)
--  Talks to YOUR Cloudflare Worker + KV key server (server-side hashing, HWID
--  auto-bind, expiry). CONFIGURE the two URLs below. Server: server-example/.
-- ============================================================================
local Junkie = {}
do
	local KEY_API  = "https://y2k-keys.y2kscript.workers.dev"  -- your deployed Worker (LIVE)
	local KEY_LINK = "https://work.ink/2Dgt/ks-int12887-kq76mlra7lo" -- work.ink key link

	local HttpService = game:GetService("HttpService")
	local function enc(s) local ok, r = pcall(function() return HttpService:UrlEncode(s) end) return ok and r or s end
	local function httpGet(u)
		for _, f in ipairs({
			function() return game:HttpGetAsync(u) end,
			function() return game:HttpGet(u) end,
			function() return request and request({ Url = u, Method = "GET" }).Body end,
		}) do
			local ok, b = pcall(f); if ok and type(b) == "string" then return b end
		end
		return nil
	end
	local function hwid()
		local id
		pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
		if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
		return tostring(id or "unknown")
	end

	function Junkie.get_key_link() return KEY_LINK end
	function Junkie.check_key(key)
		if not key or key == "" then return { valid = false, message = "No key entered" } end
		local hw = hwid()
		local url = KEY_API .. "/check?key=" .. enc(key) .. "&hwid=" .. enc(hw) .. "&t=" .. tostring(os.time())
		local body = httpGet(url)
		if not body then return { valid = false, message = "Key server unreachable" } end
		local b = string.lower(body)
		if string.find(b, "ok", 1, true) then
			getgenv().HWID = hw
			return { valid = true, message = "KEY_VALID", hwid = hw }
		elseif string.find(b, "expired", 1, true) then
			return { valid = false, message = "Key expired" }
		elseif string.find(b, "hwid", 1, true) then
			return { valid = false, message = "Key locked to another device" }
		else
			return { valid = false, message = "Invalid key" }
		end
	end
end


local TweenService = game:GetService("TweenService")
local UserInputService = game:GetService("UserInputService")
local RunService = game:GetService("RunService")
local Players = game:GetService("Players")
local Lighting = game:GetService("Lighting")
local HttpService = game:GetService("HttpService")

local Icons = {
	Shield = "rbxassetid://105619007041452",
	Loading = "rbxassetid://116535712789945",
	Lock = "rbxassetid://114355063515473",
	Key = "rbxassetid://93569468678423",
	Check = "rbxassetid://119783053916823",
	CheckCircle = "rbxassetid://10709790644",
	XCircle = "rbxassetid://10747384394",
	Warning = "rbxassetid://130226573962640",
	Globe = "rbxassetid://10734950309",
	Info = "rbxassetid://94529541997278",
	ExternalLink = "rbxassetid://71038734318580",
	Copy = "rbxassetid://107485544510830",
	Spinner = "rbxassetid://10709767827",
	Database = "rbxassetid://114209748010261",
	Sparkles = "rbxassetid://10709767827",
	ErrorFolder = "rbxassetid://113312905787220",
	Candy = "rbxassetid://10709767827",
	JunkieNewIcon = "rbxassetid://75038032192167"
}

local function hasFileSystemSupport()
    local hasWritefile = pcall(function() return type(writefile) == "function" end)
    local hasReadfile = pcall(function() return type(readfile) == "function" end)
    local hasIsfile = pcall(function() return type(isfile) == "function" end)
    return hasWritefile and hasReadfile and hasIsfile
end

local fileSystemSupported = hasFileSystemSupport()

local function saveVerifiedKey(key)
    if not fileSystemSupported then return false end
    local ok = pcall(function()
        writefile("verified_key.txt", key)
    end)
    return ok
end

local function loadVerifiedKey()
    if not fileSystemSupported then 
        return nil 
    end
    
    local ok, content = pcall(function()
        return readfile("verified_key.txt")
    end)
    
    if not ok or not content then 
        return nil 
    end
    return content
end

local function clearSavedKey()
    if not fileSystemSupported then return false end
    local ok = pcall(function() delfile("verified_key.txt") end)
    return ok
end

local Configuration = {
	ScreenGuiName = "JunkieKeySystem",
	Window = {Size = UDim2.new(0, 333, 0, 500)},
	Colors = {
		Bg = Color3.fromRGB(12, 12, 12),
		Primary = Color3.fromRGB(59, 130, 246),
		PrimaryDark = Color3.fromRGB(37, 99, 235),
		StatusIdle = Color3.fromRGB(249, 115, 22),
		StatusSuccess = Color3.fromRGB(16, 185, 129),
		StatusError = Color3.fromRGB(239, 68, 68),
		StatusVerifying = Color3.fromRGB(59, 130, 246),
		StatusWarning = Color3.fromRGB(254, 188, 46),
		TextMain = Color3.fromRGB(255, 255, 255),
		TextSec = Color3.fromRGB(161, 161, 170),
		TextMuted = Color3.fromRGB(113, 113, 122),
		Border = Color3.fromRGB(255, 255, 255),
		TrafficRed = Color3.fromRGB(255, 95, 87),
		TrafficYellow = Color3.fromRGB(254, 188, 46),
		TrafficGreen = Color3.fromRGB(40, 200, 64),
		Success = Color3.fromRGB(50, 205, 110),
		Error = Color3.fromRGB(245, 70, 90),
		Warning = Color3.fromRGB(255, 200, 50)
	},
	BorderTransparency = 0.15,
	Animations = {
		VeryFast = 0.1,
		Fast = 0.2,
		Medium = 0.4,
		Slow = 0.5,
		VerySlow = 0.6,
		Bounce = 0.6
	},
	Fonts = {
		Title = 24,
		Subtitle = 12,
		Button = 14,
		Input = 16,
		Body = 13,
		Small = 11,
		Tiny = 12
	}
}

local Utils = {}

Utils.Tween = function(obj, props, time, style, dir)
	local t =
		TweenService:Create(
		obj,
		TweenInfo.new(time or 0.3, style or Enum.EasingStyle.Quint, dir or Enum.EasingDirection.Out),
		props
	)
	t:Play()
	return t
end

Utils.CreateCorner = function(parent, radius)
	local corner = Instance.new("UICorner")
	corner.CornerRadius = UDim.new(0, radius or Configuration.CornerRadius)
	corner.Parent = parent
	return corner
end

Utils.Round = function(obj, radius)
	local c = Instance.new("UICorner")
	c.CornerRadius = UDim.new(0, radius or 12)
	c.Parent = obj
	return c
end

Utils.TweenBack = function(instance, properties, duration)
	return Utils.Tween(instance, properties, duration, Enum.EasingStyle.Back, Enum.EasingDirection.Out)
end

Utils.CreateStroke = function(parent, color, thickness, transparency)
	local stroke = Instance.new("UIStroke")
	stroke.Color = color or Configuration.Colors.Border
	stroke.Thickness = thickness or 1
	stroke.Transparency = transparency or 0.77
	stroke.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	stroke.Parent = parent
	return stroke
end

Utils.Stroke = function(obj, color, thick, trans)
	local s = Instance.new("UIStroke")
	s.Color = color or Color3.new(1, 1, 1)
	s.Thickness = thick or 1
	s.Transparency = trans or 0.9
	s.ApplyStrokeMode = Enum.ApplyStrokeMode.Border
	s.Parent = obj
	return s
end

Utils.CreateGradient = function(parent, color1, color2, rotation)
	local gradient = Instance.new("UIGradient")
	gradient.Color =
		ColorSequence.new(
		{
			ColorSequenceKeypoint.new(0, color1),
			ColorSequenceKeypoint.new(1, color2)
		}
	)
	gradient.Rotation = rotation or 300
	gradient.Parent = parent
	return gradient
end

local function SetBlur(enabled)
	local blur = Lighting:FindFirstChild("JunkieBlur")
	if enabled then
		if not blur then
			blur = Instance.new("BlurEffect")
			blur.Name = "JunkieBlur"
			blur.Size = 0
			blur.Parent = Lighting
		end
		Utils.Tween(blur, {Size = 24}, Configuration.Animations.Bounce)
	elseif blur then
		Utils.Tween(blur, {Size = 0}, Configuration.Animations.Medium)
		task.delay(
			0.4,
			function()
				blur:Destroy()
			end
		)
	end
end

local ToastSystem = {ActiveToasts = {}, MaxToasts = 3, ToastSpacing = 10}

ToastSystem.Create = function(parent, message, toastType, duration, statusCode)
	local colors = {
		success = Configuration.Colors.Success,
		error = Configuration.Colors.Error,
		warning = Configuration.Colors.Warning,
		info = Configuration.Colors.Primary
	}
	local icons = {
		success = Icons.CheckCircle,
		error = Icons.ErrorFolder,
		warning = Icons.Warning,
		info = Icons.Info
	}
	local toastColor = colors[toastType] or colors.Bg
	local toastIcon = icons[toastType] or nil
	if #ToastSystem.ActiveToasts >= ToastSystem.MaxToasts then
		local oldest = table.remove(ToastSystem.ActiveToasts, 1)
		if oldest and oldest.Parent then
			oldest:Destroy()
		end
	end
	local toastHeight = 56
	local toast = Instance.new("Frame")
	toast.Name = tick()
	toast.Size = UDim2.new(0, 0, 0, toastHeight)
	toast.Position = UDim2.new(0.5, 0, 0, 20)
	toast.AnchorPoint = Vector2.new(0.5, 0)
	toast.BackgroundColor3 = Configuration.Colors.Bg
	toast.BackgroundTransparency = 0.5
	toast.BorderSizePixel = 0
	toast.ZIndex = 300
	toast.ClipsDescendants = true
	toast.Parent = parent
	Utils.Round(toast, 14)
	Utils.CreateStroke(toast, toastColor, 1, 0.1)
	Utils.CreateGradient(toast, Configuration.Colors.Bg, Configuration.Colors.Bg, 1)
	local iconBg = Instance.new("Frame")
	iconBg.Name = "IconBg"
	iconBg.Size = UDim2.new(0, 36, 0, 36)
	iconBg.Position = UDim2.new(0, 12, 0.5, 0)
	iconBg.AnchorPoint = Vector2.new(0, 0.5)
	iconBg.BackgroundColor3 = toastColor
	iconBg.BackgroundTransparency = 0.85
	iconBg.BorderSizePixel = 0
	iconBg.ZIndex = 301
	iconBg.Parent = toast
	Utils.Round(iconBg, 18)
	local icon = Instance.new("ImageLabel")
	icon.Name = "Icon"
	icon.Size = UDim2.new(0, 20, 0, 20)
	icon.Position = UDim2.new(0.5, 0, 0.5, 0)
	icon.AnchorPoint = Vector2.new(0.5, 0.5)
	icon.BackgroundTransparency = 1
	icon.Image = toastIcon
	icon.ImageColor3 = toastColor
	icon.ZIndex = 302
	icon.Parent = iconBg
	local textContainer = Instance.new("Frame")
	textContainer.Name = "TextContainer"
	textContainer.Size = UDim2.new(1, statusCode and -110 or -60, 1, 0)
	textContainer.Position = UDim2.new(0, 56, 0, 0)
	textContainer.BackgroundTransparency = 1
	textContainer.ZIndex = 301
	textContainer.Parent = toast
	local text = Instance.new("TextLabel")
	text.Name = "Message"
	text.Size = UDim2.new(1, 0, 1, 0)
	text.BackgroundTransparency = 1
	text.Text = message or ""
	text.TextColor3 = Configuration.Colors.TextMain
	text.TextSize = Configuration.Fonts.Body
	text.Font = Enum.Font.GothamMedium
	text.TextXAlignment = Enum.TextXAlignment.Left
	text.TextYAlignment = Enum.TextYAlignment.Center
	text.TextWrapped = true
	text.ZIndex = 301
	text.Parent = textContainer
	if statusCode then
		local statusBadge = Instance.new("Frame")
		statusBadge.Name = "StatusBadge"
		statusBadge.Size = UDim2.new(0, 44, 0, 28)
		statusBadge.Position = UDim2.new(1, -12, 0.5, 0)
		statusBadge.AnchorPoint = Vector2.new(1, 0.5)
		statusBadge.BackgroundColor3 = toastColor
		statusBadge.BackgroundTransparency = 0.8
		statusBadge.BorderSizePixel = 0
		statusBadge.ZIndex = 301
		statusBadge.Parent = toast
		Utils.Round(statusBadge, 8)
		Utils.CreateStroke(statusBadge, toastColor, 1, Configuration.BorderTransparency)
		local statusCodeLabel = Instance.new("TextLabel")
		statusCodeLabel.Name = "StatusCode"
		statusCodeLabel.Size = UDim2.new(1, 0, 1, 0)
		statusCodeLabel.BackgroundTransparency = 1
		statusCodeLabel.Text = tostring(statusCode)
		statusCodeLabel.TextColor3 = toastColor
		statusCodeLabel.TextSize = Configuration.Fonts.Small
		statusCodeLabel.Font = Enum.Font.GothamBold
		statusCodeLabel.ZIndex = 302
		statusCodeLabel.Parent = statusBadge
	end
	table.insert(ToastSystem.ActiveToasts, toast)
	ToastSystem.RepositionToasts()
	local targetWidth = 320
	Utils.TweenBack(toast, {Size = UDim2.new(0, targetWidth, 0, toastHeight)}, Configuration.Animations.Medium)
	task.delay(
		duration or 3.5,
		function()
			if toast.Parent then
				Utils.Tween(
					toast,
					{
						Position = UDim2.new(0.5, 0, 0, -80),
						BackgroundTransparency = 1
					},
					Configuration.Animations.Medium
				)
				for i, t in ipairs(ToastSystem.ActiveToasts) do
					if t == toast then
						table.remove(ToastSystem.ActiveToasts, i)
						break
					end
				end
				task.wait(Configuration.Animations.Medium)
				toast:Destroy()
				ToastSystem.RepositionToasts()
			end
		end
	)
	return toast
end

ToastSystem.RepositionToasts = function()
	for i, toast in ipairs(ToastSystem.ActiveToasts) do
		local targetY = 20 + ((i - 1) * (60 + ToastSystem.ToastSpacing))
		Utils.Tween(toast, {Position = UDim2.new(0.5, 0, 0, targetY)}, Configuration.Animations.Medium)
	end
end

local function Build()
	local parent = game:GetService("CoreGui")
	local old = parent:FindFirstChild(Configuration.ScreenGuiName)
	if old then
		old:Destroy()
	end
	local screen = Instance.new("ScreenGui")
	screen.Name = Configuration.ScreenGuiName
	screen.ResetOnSpawn = false
	screen.Parent = parent

	-- Discord banner (top of screen, transparent, blinking + glow)
	local discordBanner = Instance.new("TextLabel")
	discordBanner.Name = "DiscordBanner"
	discordBanner.Size = UDim2.new(0, 400, 0, 32)
	discordBanner.Position = UDim2.new(0.5, 0, 0, 10)
	discordBanner.AnchorPoint = Vector2.new(0.5, 0)
	discordBanner.BackgroundTransparency = 1
	discordBanner.Text = "Join https://discord.gg/EFFKrfFkPQ"
	discordBanner.TextColor3 = Color3.fromRGB(88, 101, 242)
	discordBanner.TextSize = 16
	discordBanner.Font = Enum.Font.GothamBold
	discordBanner.TextTransparency = 0
	discordBanner.Parent = screen

	local bannerStroke = Instance.new("UIStroke")
	bannerStroke.Color = Color3.fromRGB(88, 101, 242)
	bannerStroke.Thickness = 2
	bannerStroke.Transparency = 0.3
	bannerStroke.Parent = discordBanner

	task.spawn(function()
		while discordBanner and discordBanner.Parent do
			Utils.Tween(discordBanner, {TextTransparency = 0.4}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.7}, 0.6)
			task.wait(0.6)
			Utils.Tween(discordBanner, {TextTransparency = 0}, 0.6)
			Utils.Tween(bannerStroke, {Transparency = 0.3}, 0.6)
			task.wait(0.6)
		end
	end)

	local overlay = Instance.new("Frame")
	overlay.Size = UDim2.fromScale(1, 1)
	overlay.BackgroundColor3 = Color3.new(0, 0, 0)
	overlay.BackgroundTransparency = 1
	overlay.Parent = screen
	Utils.Tween(overlay, {BackgroundTransparency = 1}, 1)
	SetBlur(true)
	local main = Instance.new("Frame")
	main.Size = Configuration.Window.Size
	main.Position = UDim2.new(0.5, 0, 0.5, 60)
	main.AnchorPoint = Vector2.new(0.5, 0.5)
	main.BackgroundColor3 = Configuration.Colors.Bg
	main.BackgroundTransparency = 0.2
	main.ClipsDescendants = true
	main.Parent = screen
	Utils.Round(main, 24)
	Utils.Stroke(main, Color3.new(1, 1, 1), 1, 0.92)
	local glass = Instance.new("Frame")
	glass.Size = UDim2.fromScale(1, 1)
	glass.BackgroundColor3 = Color3.new(1, 1, 1)
	glass.BackgroundTransparency = 0.985
	glass.ZIndex = 0
	glass.Parent = main
	Utils.Round(glass, 24)
	local bar = Instance.new("Frame")
	bar.Size = UDim2.new(1, 0, 0, 54)
	bar.BackgroundTransparency = 1
	bar.Parent = main
	local dots = Instance.new("Frame")
	dots.Size = UDim2.new(0, 54, 0, 12)
	dots.Position = UDim2.new(0, 20, 0.5, 0)
	dots.AnchorPoint = Vector2.new(0, 0.5)
	dots.BackgroundTransparency = 1
	dots.Parent = bar
	local dColors = {
		Configuration.Colors.TrafficRed,
		Configuration.Colors.TrafficYellow,
		Configuration.Colors.TrafficGreen
	}
	for i, c in ipairs(dColors) do
		local d = Instance.new("Frame")
		d.Size = UDim2.fromOffset(12, 12)
		d.Position = UDim2.fromOffset((i - 1) * 18, 0)
		d.BackgroundColor3 = c
		d.BorderSizePixel = 0
		d.Parent = dots
		Utils.Round(d, 6)
	end
	local titleText = Instance.new("TextLabel")
	titleText.Size = UDim2.new(1, 0, 1, 0)
	titleText.Text = "JUNKIE"
	titleText.TextColor3 = Color3.new(1, 1, 1)
	titleText.TextTransparency = 0.7
	titleText.TextSize = 10
	titleText.Font = Enum.Font.GothamBold
	titleText.BackgroundTransparency = 1
	titleText.Parent = bar
	local content = Instance.new("ScrollingFrame")
	content.Size = UDim2.new(1, 0, 1, -54)
	content.Position = UDim2.new(0, 0, 0, 54)
	content.BackgroundTransparency = 1
	content.ScrollBarThickness = 0
	content.CanvasSize = UDim2.new(0, 0, 0, 440)
	content.Parent = main
	local list = Instance.new("UIListLayout")
	list.Padding = UDim.new(0, 24)
	list.HorizontalAlignment = Enum.HorizontalAlignment.Center
	list.Parent = content
	local pad = Instance.new("UIPadding")
	pad.PaddingTop = UDim.new(0, 5)
	pad.Parent = content
	local logoContainer = Instance.new("Frame")
	logoContainer.Size = UDim2.fromOffset(80, 80)
	logoContainer.BackgroundColor3 = Configuration.Colors.Primary
	logoContainer.Parent = content
	Utils.Round(logoContainer, 20)
	local grad = Instance.new("UIGradient")
	grad.Color = ColorSequence.new(Configuration.Colors.Primary, Configuration.Colors.PrimaryDark)
	grad.Rotation = 45
	grad.Parent = logoContainer
	local sIcon = Instance.new("ImageLabel")
	sIcon.Size = UDim2.fromScale(1, 1)
	sIcon.Position = UDim2.fromScale(0.5, 0.5)
	sIcon.AnchorPoint = Vector2.new(0.5, 0.5)
	sIcon.Image = Icons.JunkieNewIcon
	sIcon.ScaleType = Enum.ScaleType.Fit
	sIcon.BackgroundTransparency = 1
	sIcon.Parent = logoContainer
	local titleArea = Instance.new("Frame")
	titleArea.Size = UDim2.new(1, 0, 0, 44)
	titleArea.BackgroundTransparency = 1
	titleArea.Parent = content
	local mainTitle = Instance.new("TextLabel")
	mainTitle.Size = UDim2.new(1, 0, 0, 26)
	mainTitle.Text = "Junkie"
	mainTitle.TextColor3 = Color3.new(1, 1, 1)
	mainTitle.TextSize = 26
	mainTitle.Font = Enum.Font.GothamBold
	mainTitle.BackgroundTransparency = 1
	mainTitle.Parent = titleArea
	local subTitle = Instance.new("TextLabel")
	subTitle.Size = UDim2.new(1, 0, 0, 16)
	subTitle.Position = UDim2.fromOffset(0, 28)
	subTitle.Text = "junkie-development.de"
	subTitle.TextColor3 = Configuration.Colors.TextSec
	subTitle.TextSize = 13
	subTitle.Font = Enum.Font.Gotham
	subTitle.BackgroundTransparency = 1
	subTitle.Parent = titleArea
	local statusCard = Instance.new("Frame")
	statusCard.Size = UDim2.new(0, 280, 0, 68)
	statusCard.BackgroundColor3 = Color3.new(1, 1, 1)
	statusCard.BackgroundTransparency = 0.96
	statusCard.Parent = content
	Utils.Round(statusCard, 16)
	local sStroke = Utils.Stroke(statusCard, Color3.new(1, 1, 1), 1, 0.95)
	local sIconBg = Instance.new("Frame")
	sIconBg.Size = UDim2.fromOffset(42, 42)
	sIconBg.Position = UDim2.new(0, 14, 0.5, 0)
	sIconBg.AnchorPoint = Vector2.new(0, 0.5)
	sIconBg.BackgroundColor3 = Configuration.Colors.StatusIdle
	sIconBg.BackgroundTransparency = 0.9
	sIconBg.Parent = statusCard
	Utils.Round(sIconBg, 21)
	local sImg = Instance.new("ImageLabel")
	sImg.Size = UDim2.fromScale(0.5, 0.5)
	sImg.Position = UDim2.fromScale(0.5, 0.5)
	sImg.AnchorPoint = Vector2.new(0.5, 0.5)
	sImg.Image = Icons.Lock
	sImg.ImageColor3 = Configuration.Colors.StatusIdle
	sImg.BackgroundTransparency = 1
	sImg.Parent = sIconBg
	local sLabel = Instance.new("TextLabel")
	sLabel.Size = UDim2.new(1, -70, 0, 14)
	sLabel.Position = UDim2.fromOffset(70, 16)
	sLabel.Text = "CURRENT STATUS"
	sLabel.TextColor3 = Configuration.Colors.TextMuted
	sLabel.TextSize = 10
	sLabel.Font = Enum.Font.GothamBold
	sLabel.TextXAlignment = Enum.TextXAlignment.Left
	sLabel.BackgroundTransparency = 1
	sLabel.Parent = statusCard
	local sValue = Instance.new("TextLabel")
	sValue.Size = UDim2.new(1, -70, 0, 20)
	sValue.Position = UDim2.fromOffset(70, 32)
	sValue.Text = "No key detected"
	sValue.TextColor3 = Configuration.Colors.StatusIdle
	sValue.TextSize = 15
	sValue.Font = Enum.Font.GothamMedium
	sValue.TextXAlignment = Enum.TextXAlignment.Left
	sValue.BackgroundTransparency = 1
	sValue.Parent = statusCard
	local inputFrame = Instance.new("Frame")
	inputFrame.Size = UDim2.new(0, 280, 0, 52)
	inputFrame.BackgroundColor3 = Color3.new(1, 1, 1)
	inputFrame.BackgroundTransparency = 0.975
	inputFrame.Parent = content
	Utils.Round(inputFrame, 14)
	local iStroke = Utils.Stroke(inputFrame, Color3.new(1, 1, 1), 1, 0.95)
	local kIcon = Instance.new("ImageLabel")
	kIcon.Size = UDim2.fromOffset(18, 18)
	kIcon.Position = UDim2.new(0, 14, 0.5, 0)
	kIcon.AnchorPoint = Vector2.new(0, 0.5)
	kIcon.Image = Icons.Key
	kIcon.ImageColor3 = Configuration.Colors.TextMuted
	kIcon.BackgroundTransparency = 1
	kIcon.Parent = inputFrame
	local box = Instance.new("TextBox")
	box.Size = UDim2.new(1, -85, 1, 0)
	box.Position = UDim2.fromOffset(45, 0)
	box.Text = ""
	box.PlaceholderText = "Enter your key..."
	box.TextColor3 = Color3.new(1, 1, 1)
	box.TextSize = 14
	box.Font = Enum.Font.Gotham
	box.BackgroundTransparency = 1
	box.TextXAlignment = Enum.TextXAlignment.Left
	box.Parent = inputFrame
	local paste = Instance.new("ImageButton")
	paste.Size = UDim2.fromOffset(18, 18)
	paste.Position = UDim2.new(1, -14, 0.5, 0)
	paste.AnchorPoint = Vector2.new(1, 0.5)
	paste.Image = Icons.Copy
	paste.ImageColor3 = Configuration.Colors.TextMuted
	paste.BackgroundTransparency = 1
	paste.Parent = inputFrame
	local btnRow = Instance.new("Frame")
	btnRow.Size = UDim2.new(0, 280, 0, 50)
	btnRow.BackgroundTransparency = 1
	btnRow.Parent = content
	local redeem = Instance.new("TextButton")
	redeem.Size = UDim2.new(0.5, -8, 1, 0)
	redeem.BackgroundColor3 = Configuration.Colors.Primary
	redeem.Text = "Redeem"
	redeem.TextColor3 = Color3.new(1, 1, 1)
	redeem.Font = Enum.Font.GothamBold
	redeem.TextSize = 14
	redeem.AutoButtonColor = false
	redeem.Parent = btnRow
	Utils.Round(redeem, 14)
	local getKey = Instance.new("TextButton")
	getKey.Size = UDim2.new(0.5, -8, 1, 0)
	getKey.Position = UDim2.new(0.5, 8, 0, 0)
	getKey.BackgroundColor3 = Color3.new(1, 1, 1)
	getKey.BackgroundTransparency = 0.955
	getKey.Text = "Get Key"
	getKey.TextColor3 = Color3.new(1, 1, 1)
	getKey.Font = Enum.Font.GothamBold
	getKey.TextSize = 14
	getKey.AutoButtonColor = false
	getKey.Parent = btnRow
	Utils.Round(getKey, 14)
	Utils.Stroke(getKey, Color3.new(1, 1, 1), 1, 0.94)
	local function ApplyHover(btn)
		local baseColor = btn.BackgroundColor3
		btn.MouseEnter:Connect(
			function()
				Utils.Tween(
					btn,
					{
						BackgroundColor3 = baseColor:Lerp(Color3.new(1, 1, 1), 0.1)
					},
					0.2
				)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset + 4, btn.Size.Y.Scale, btn.Size.Y.Offset + 2)
					},
					0.2
				)
			end
		)
		btn.MouseLeave:Connect(
			function()
				Utils.Tween(btn, {BackgroundColor3 = baseColor}, 0.2)
				Utils.Tween(
					btn,
					{
						Size = UDim2.new(btn.Size.X.Scale, btn.Size.X.Offset - 4, btn.Size.Y.Scale, btn.Size.Y.Offset - 2)
					},
					0.2
				)
			end
		)
	end
	ApplyHover(redeem)
	ApplyHover(getKey)
	box.Focused:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.5, Thickness = 1.2}, 0.3)
		end
	)
	box.FocusLost:Connect(
		function()
			Utils.Tween(iStroke, {Transparency = 0.95, Thickness = 1}, 0.3)
		end
	)
	local spinConnection
	local dotsThread
	local function SetStatus(state)
		if spinConnection then
			spinConnection:Disconnect()
			spinConnection = nil
			sImg.Rotation = 0
		end
		if dotsThread then
			task.cancel(dotsThread)
			dotsThread = nil
		end
		local color = Configuration.Colors.StatusIdle
		local icon = Icons.Lock
		local text = "No key detected"
		if state == "verifying" then
			color = Configuration.Colors.StatusVerifying
			icon = Icons.Loading
			text = "Verifying access"
			spinConnection =
				RunService.Heartbeat:Connect(
				function(dt)
					if not sImg or not sImg.Parent then
						if spinConnection then
							spinConnection:Disconnect()
						end
						spinConnection = nil
						return
					end
					sImg.Rotation = (sImg.Rotation + dt * 360) % 360
				end
			)
			local dots = {".", "..", "...", ""}
			local i = 1
			dotsThread =
				task.spawn(
				function()
					while sValue and sValue.Parent do
						if not sValue.Text:find("Verifying access", 1, true) then
							break
						end
						sValue.Text = text .. dots[i]
						i = (i % #dots) + 1
						task.wait(0.45)
					end
				end
			)
		elseif state == "success" then
			color = Configuration.Colors.StatusSuccess
			icon = Icons.CheckCircle
			text = "Access Granted"
		elseif state == "error" then
			color = Configuration.Colors.StatusError
			icon = Icons.XCircle
			text = "Invalid Key"
		end
		Utils.Tween(sValue, {TextColor3 = color}, 0.35)
		Utils.Tween(sImg, {ImageColor3 = color}, 0.35)
		Utils.Tween(sIconBg, {BackgroundColor3 = color}, 0.35)
		sValue.Text = text
		sImg.Image = icon
	end
	redeem.MouseButton1Click:Connect(
		function()
			local key = (box.Text:gsub("%s+", "")) -- trim spaces; keep case (work.ink tokens are lowercase)
			SetStatus("verifying")
			redeem.Text = "..."
			redeem.Active = false
            local result = Junkie.check_key(key)
			redeem.Active = true
			redeem.Text = "Redeem"
			if not result then
				SetStatus("error")
				ToastSystem.Create(screen, "API request failed: " .. tostring(result), "error")
				return
			end
			if result.valid then
                saveVerifiedKey(key)
                getgenv().SCRIPT_KEY = key
                SetStatus("success")
                ToastSystem.Create(screen, "Access granted!", "success", nil, status)
                task.wait(0.8)
                SetBlur(false)
                Utils.Tween(
                    main,
                    {
                        Position = UDim2.new(0.5, 0, 0.5, 100),
                        BackgroundTransparency = 1
                    },
                    0.7,
                    Enum.EasingStyle.Exponential,
                    Enum.EasingDirection.In
                )
                task.delay(
                    0.7,
                    function()
                        screen:Destroy()
                    end
                )
			else
				SetStatus("error")
				ToastSystem.Create(screen, result.message or "Invalid key", "error", nil, status)
			end
		end
	)
	getKey.MouseButton1Click:Connect(
		function()
			setclipboard(Junkie.get_key_link())
			ToastSystem.Create(screen, "Key link has been copied to clipboard", "success")
		end
	)
	paste.MouseButton1Click:Connect(
		function()
			ToastSystem.Create(screen, "Paste functionality not supported in Roblox (security reasons)", "warning")
		end
	)
	main.Position = UDim2.new(0.5, 0, 0.5, 100)
	main.BackgroundTransparency = 1
	Utils.Tween(
		main,
		{
			Position = UDim2.new(0.5, 0, 0.5, 0),
			BackgroundTransparency = 0.2
		},
		1,
		Enum.EasingStyle.Exponential
	)
	local dragging, dragStart, startPos
	bar.InputBegan:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = true
				dragStart = input.Position
				startPos = main.Position
			end
		end
	)
	UserInputService.InputChanged:Connect(
		function(input)
			if dragging and input.UserInputType == Enum.UserInputType.MouseMovement then
				local delta = input.Position - dragStart
				main.Position =
					UDim2.new(startPos.X.Scale, startPos.X.Offset + delta.X, startPos.Y.Scale, startPos.Y.Offset + delta.Y)
			end
		end
	)
	UserInputService.InputEnded:Connect(
		function(input)
			if input.UserInputType == Enum.UserInputType.MouseButton1 then
				dragging = false
			end
		end
	)
	return screen
end

local savedKey = loadVerifiedKey()
local keyToCheck = savedKey
if not keyToCheck then
    keyToCheck = getgenv().SCRIPT_KEY
end

local result = Junkie.check_key(keyToCheck)
if result and result.valid then
    if result.message == "KEYLESS" then
        getgenv().SCRIPT_KEY = "KEYLESS"
    elseif result.message == "KEY_VALID" then
        if not savedKey and keyToCheck then
            saveVerifiedKey(keyToCheck)
        end
        getgenv().SCRIPT_KEY = keyToCheck
    else
        Build()
    end
else
    Build()
end

while not getgenv().SCRIPT_KEY do
    task.wait(0.1)
end
end
__y2k_keygate()
-- ===== Protected payload =====
-- Protected with Vm runtime. Tampering halts execution.
-- Vm protection runtime (bundled). Do not edit by hand.
local Crypt = (function()
--!nonstrict
-- ============================================================================
--  Crypt.lua  --  lightweight obfuscation / integrity primitives
--  Part of the Vm protection runtime. No external deps. Luau-safe.
--
--  Provides: XOR string cipher, FNV-1a hash, base64, and a small PRNG so the
--  runtime can hide embedded strings (URLs, function names) and verify
--  integrity without leaving plaintext secrets in the bytecode.
-- ============================================================================

local Crypt = {}

local schar, sbyte, ssub, srep = string.char, string.byte, string.sub, string.rep
local tconcat = table.concat
local bxor = bit32 and bit32.bxor or function(a, b)
	local r, p = 0, 1
	while a > 0 or b > 0 do
		local x, y = a % 2, b % 2
		if x ~= y then r = r + p end
		a, b, p = (a - x) / 2, (b - y) / 2, p * 2
	end
	return r
end

-- 32-bit multiply mod 2^32 that stays within double precision (2^53).
-- Splitting the accumulator into hi/lo 16-bit halves keeps every intermediate
-- product under 2^42, so no precision is lost (a plain h*16777619 overflows 2^53).
local function mul32(a, b)
	local ah = (a - a % 65536) / 65536   -- floor(a / 2^16), < 2^16
	local al = a % 65536                  -- a mod 2^16, < 2^16
	return ((ah * b % 65536) * 65536 + al * b) % 4294967296
end

-- FNV-1a 32-bit hash of a string (used for integrity fingerprints)
function Crypt.hash(s)
	local h = 2166136261
	for i = 1, #s do
		h = bxor(h, sbyte(s, i))
		h = mul32(h, 16777619)
	end
	return h
end

-- repeating-key XOR cipher (symmetric). key is a string.
function Crypt.xor(data, key)
	local out, kl = {}, #key
	for i = 1, #data do
		out[i] = schar(bxor(sbyte(data, i), sbyte(key, (i - 1) % kl + 1)))
	end
	return tconcat(out)
end

-- deterministic PRNG (xorshift) seeded from a string; for shuffling/jitter
function Crypt.rng(seed)
	local state = (type(seed) == "string") and Crypt.hash(seed) or (seed or 0x1234567)
	if state == 0 then state = 0x9E3779B9 end
	return function()
		state = bxor(state, (state * 32) % 4294967296)
		state = bxor(state, math.floor(state / 8))
		state = bxor(state, (state * 16384) % 4294967296)
		state = state % 4294967296
		return state / 4294967296
	end
end

-- base64 (so ciphertext survives as a string literal in the bundle)
local B64 = "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/"
function Crypt.b64encode(data)
	local out = {}
	for i = 1, #data, 3 do
		local a, b, c = sbyte(data, i), sbyte(data, i + 1), sbyte(data, i + 2)
		local n = a * 65536 + (b or 0) * 256 + (c or 0)
		local c1 = math.floor(n / 262144) % 64
		local c2 = math.floor(n / 4096) % 64
		local c3 = math.floor(n / 64) % 64
		local c4 = n % 64
		out[#out + 1] = ssub(B64, c1 + 1, c1 + 1)
		out[#out + 1] = ssub(B64, c2 + 1, c2 + 1)
		out[#out + 1] = b and ssub(B64, c3 + 1, c3 + 1) or "="
		out[#out + 1] = c and ssub(B64, c4 + 1, c4 + 1) or "="
	end
	return tconcat(out)
end

local B64I
function Crypt.b64decode(data)
	if not B64I then
		B64I = {}
		for i = 1, #B64 do B64I[ssub(B64, i, i)] = i - 1 end
	end
	data = string.gsub(data, "[^" .. B64 .. "]", "")
	local out = {}
	for i = 1, #data, 4 do
		local a = B64I[ssub(data, i, i)] or 0
		local b = B64I[ssub(data, i + 1, i + 1)] or 0
		local c = B64I[ssub(data, i + 2, i + 2)]
		local d = B64I[ssub(data, i + 3, i + 3)]
		local n = a * 262144 + b * 4096 + (c or 0) * 64 + (d or 0)
		out[#out + 1] = schar(math.floor(n / 65536) % 256)
		if c then out[#out + 1] = schar(math.floor(n / 256) % 256) end
		if d then out[#out + 1] = schar(n % 256) end
	end
	return tconcat(out)
end

-- convenience: encrypt a plaintext to a portable token (b64(xor(data,key)))
function Crypt.seal(plaintext, key)
	return Crypt.b64encode(Crypt.xor(plaintext, key))
end
function Crypt.open(token, key)
	return Crypt.xor(Crypt.b64decode(token), key)
end

return Crypt

end)()
local Secure = (function()
--!nonstrict
-- ============================================================================
--  Secure.lua  --  capture real executor functions & expose protected proxies
--
--  THE CORE PROTECTION. At load time (before any spy can install hooks) we grab
--  references to the real executor functions into PRIVATE upvalues, then hand
--  the wrapped script only thin proxies. Because the proxies call the captured
--  originals directly, a spy that later hooks the GLOBAL `request` / `http` /
--  `readfile` never sees the script's calls -- they bypass the global.
--
--  Proxies are wrapped with newcclosure so they read as native C-closures:
--  iscclosure() passes, and getupvalues() is blocked on them by most executors,
--  hiding the captured originals from getgc/upvalue inspection.
-- ============================================================================

local Secure = {}

-- resolve the real global table as early as possible
local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local rawget, rawset = rawget, rawset
local iscc = iscclosure
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction or function(f) return f end

-- list of sensitive globals we proxy. (function-valued globals only)
local CAPTURE = {
	"request", "http_request", "readfile", "writefile", "appendfile", "isfile",
	"isfolder", "listfiles", "makefolder", "delfile", "delfolder", "loadstring",
	"getgenv", "getrawmetatable", "setrawmetatable", "hookfunction", "hookmetamethod",
	"newcclosure", "getnamecallmethod", "setclipboard", "queue_on_teleport",
	"getcustomasset", "fireclickdetector", "firetouchinterest", "fireproximityprompt",
	"isexecutorclosure", "checkcaller", "getconnections", "getcallingscript",
}

-- Capture the real functions. Returns a PRIVATE table (kept as an upvalue by the
-- caller -- never store this in a global).
function Secure.capture()
	local raw = {}

	-- http via the common executor spellings, in priority order
	raw.http = (syn and syn.request) or (http and http.request) or http_request or request
	-- guard: if http appears already hooked (became an l-closure), remember it
	raw.http_tampered = (iscc and raw.http and not iscc(raw.http)) or false

	for _, name in ipairs(CAPTURE) do
		local fn = rawget(realG, name)
		if type(fn) == "function" then
			-- clone where supported so even a later identity-swap of the global
			-- can't reach our reference
			local ok, c = pcall(clonef, fn)
			raw[name] = ok and c or fn
			raw[name .. "_genuine"] = (iscc and iscc(fn)) or false
		end
	end

	-- HttpGet/HttpGetAsync live on `game`; capture bound callers
	local okGame = pcall(function() return game and game.HttpGet end)
	if okGame and game then
		raw.HttpGet = function(url, ...) return game:HttpGet(url, ...) end
		raw.HttpGetAsync = function(url, ...) return game:HttpGetAsync(url, ...) end
	end

	return raw
end

-- Build the proxy table the sandbox exposes. `raw` is the private capture.
-- Each proxy is a newcclosure so its upvalues (the real fn) are not inspectable.
function Secure.proxies(raw)
	local P = {}

	local function wrap(realFn)
		if type(realFn) ~= "function" then return nil end
		return newcc(function(...) return realFn(...) end)
	end

	-- generic passthrough proxies
	for _, name in ipairs(CAPTURE) do
		if raw[name] then P[name] = wrap(raw[name]) end
	end

	-- unified HTTP proxy (the prime spy target). Accepts the standard {Url=...}.
	if raw.http then
		local http = raw.http
		P.request = newcc(function(opts) return http(opts) end)
		P.http_request = P.request
		if syn then P.syn = { request = P.request } end
	end
	if raw.HttpGet then
		P.HttpGet = newcc(function(url, ...) return raw.HttpGet(url, ...) end)
		P.HttpGetAsync = newcc(function(url, ...) return raw.HttpGetAsync(url, ...) end)
	end

	return P
end

-- Snapshot identities so Integrity can detect later replacement of our proxies.
function Secure.fingerprint(P)
	local fp = {}
	for k, v in pairs(P) do
		if type(v) == "function" then fp[k] = v end
	end
	return fp
end

return Secure

end)()
local Environment = (function()
--!nonstrict
-- ============================================================================
--  Environment.lua  --  the sealed sandbox the wrapped script runs inside
--
--  Builds a custom _ENV whose:
--    * function-valued executor globals resolve to PROTECTED PROXIES
--    * everything else falls through to the real globals (so game, workspace,
--      Instance, math, string, task, etc. all work -- full Luau semantics)
--    * writes stay local to the sandbox (script can't pollute real _G)
--    * the metatable is private (Integrity verifies it wasn't swapped)
--
--  This is the isolation layer: the script believes it has a normal global
--  environment, but its sensitive calls are routed through the Vm.
-- ============================================================================

local Environment = {}

function Environment.build(proxies, realG)
	realG = realG or (getgenv and getgenv()) or _G

	-- the sandbox's own storage for globals the script defines
	local store = {}

	-- private metatable (kept out of the sandbox; Integrity holds a ref)
	local mt = {}

	mt.__index = function(_, key)
		-- 1. protected proxy?
		local p = proxies[key]
		if p ~= nil then return p end
		-- 2. script-local global?
		local s = store[key]
		if s ~= nil then return s end
		-- 3. fall through to the real environment
		return realG[key]
	end

	mt.__newindex = function(_, key, value)
		-- keep all writes inside the sandbox (never touch real globals)
		store[key] = value
	end

	-- unique private lock token. __metatable makes getmetatable(env) return THIS
	-- (hiding the real mt) and makes setmetatable(env, ...) error -- so the env's
	-- metatable cannot be swapped. Integrity verifies this token is still in place.
	local lock = {}
	mt.__metatable = lock

	local env = setmetatable({}, mt)

	-- expose a sandboxed getfenv/getgenv so the script's own introspection
	-- returns the sandbox, not the real globals (don't leak the boundary)
	store.getgenv = function() return env end
	store._G = env
	store.shared = store.shared or {}

	return env, mt, store, lock
end

return Environment

end)()
local Integrity = (function()
--!nonstrict
-- ============================================================================
--  Integrity.lua  --  anti-tamper / anti-penetration
--
--  Verifies the runtime hasn't been hooked or swapped, both at startup and via
--  a background watchdog. On tamper it triggers a caller-supplied onTamper
--  (the Vm wipes the sandbox + halts).
--
--  Checks:
--   * capture genuineness   -- were the executor funcs already hooked at capture?
--   * proxy identity         -- have our proxies been replaced since fingerprint?
--   * env seal               -- is the sandbox __index/__newindex intact?
--   * hostile introspection  -- is something actively decompiling/hooking us?
--   * source checksum        -- does the protected payload still match?
-- ============================================================================

local Integrity = {}

local iscc = iscclosure
local getus = getupvalues or (debug and debug.getupvalues)

-- 1. Were any captured executor functions already hooks (l-closures) at capture?
function Integrity.checkCapture(raw)
	local suspicious = {}
	if raw.http_tampered then suspicious[#suspicious + 1] = "http" end
	for k, v in pairs(raw) do
		if string.sub(k, -8) == "_genuine" and v == false then
			suspicious[#suspicious + 1] = string.sub(k, 1, -9)
		end
	end
	return suspicious
end

-- 2. Our proxies must still be the exact functions we created.
function Integrity.checkProxies(P, fingerprint)
	for k, original in pairs(fingerprint) do
		if P[k] ~= original then return false, k end
	end
	return true
end

-- 3. The sandbox env metatable must be intact (not re-pointed to leak globals).
function Integrity.checkEnv(env, expectedMT)
	local mt = getmetatable(env)
	if mt ~= expectedMT then return false, "metatable" end
	return true
end

-- 4. Best-effort: detect if our own proxies have become inspectable (a sign a
--    de-hook tool unwrapped the cclosure). On a healthy executor getupvalues on
--    a newcclosure should be empty/blocked; non-empty => someone unwrapped it.
function Integrity.checkOpaque(P)
	if not getus then return true end
	for _, v in pairs(P) do
		if type(v) == "function" then
			local ok, ups = pcall(getus, v)
			if ok and type(ups) == "table" and next(ups) ~= nil then
				return false
			end
		end
	end
	return true
end

-- run all startup checks; returns ok, reason
function Integrity.startup(ctx)
	local sus = Integrity.checkCapture(ctx.raw)
	if #sus > 0 and ctx.strict then
		return false, "capture-hooked:" .. table.concat(sus, ",")
	end
	local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
	if not okP then return false, "proxy-swapped:" .. tostring(badKey) end
	local okE, why = Integrity.checkEnv(ctx.env, ctx.envLock)
	if not okE then return false, "env-" .. tostring(why) end
	if not Integrity.checkOpaque(ctx.proxies) then return false, "opaque-broken" end
	return true
end

-- background watchdog: re-run cheap checks on an interval and self-destruct.
-- Spawns through the Memory scope (ctx.mem) so the thread is tracked and
-- cancelled on cleanup -- it can never leak past the script's lifetime.
function Integrity.watchdog(ctx, onTamper)
	local wait_ = (task and task.wait) or wait
	local body = function()
		while ctx.alive do
			wait_(ctx.interval or 2)
			if not ctx.alive then return end
			local okP, badKey = Integrity.checkProxies(ctx.proxies, ctx.fingerprint)
			local okE = Integrity.checkEnv(ctx.env, ctx.envLock)
			if not okP or not okE then
				ctx.alive = false
				pcall(onTamper, okP and "env" or ("proxy:" .. tostring(badKey)))
				return
			end
		end
	end
	if ctx.mem and ctx.mem.spawn then
		ctx.mem:spawn(body)
	else
		local spawn = (task and task.spawn) or spawn
		if spawn then spawn(body) end
	end
end

return Integrity

end)()
local Stealth = (function()
--!nonstrict
-- ============================================================================
--  Stealth.lua  --  comprehensive environment spoofing / anti-detection
--
--  Covers the full sUNC executor surface (docs.sunc.su). For each function an
--  anti-cheat could use to fingerprint the executor, detect hooks, or scan for
--  injected objects, we install a fake that answers "clean" -- while leaving the
--  function usable for everyone else.
--
--  Technique: hookfunction (rewrites the function OBJECT, so even a reference
--  the AC captured early is affected), replacement wrapped in newcclosure (stays
--  a C-closure -> passes iscclosure). Everything pcall-guarded; only spoofs what
--  the executor actually exposes.
--
--  HONEST: beats ACs that read these globals at runtime and trust them. Does NOT
--  beat an AC that ran fully before you, re-implements checks in its own VM, or
--  validates server-side. Raises the bar across games.
-- ============================================================================

local Stealth = {}

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local newcc = newcclosure or function(f) return f end
local clonef = clonefunction
local hookf = hookfunction
local cloneref_ = cloneref or function(x) return x end
local rawget, rawset = rawget, rawset

-- private registries (weak so we never pin objects alive)
local hiddenObjs = setmetatable({}, { __mode = "k" })  -- hide from gc/instance scans
local genuineFns = setmetatable({}, { __mode = "k" })  -- report as un-hooked / ours
local ourScripts = setmetatable({}, { __mode = "k" })  -- hide script bytecode/closure
local installed  = false

function Stealth.hide(o)        if o ~= nil then hiddenObjs[o] = true end return o end
function Stealth.markGenuine(f) if type(f) == "function" then genuineFns[f] = true end return f end
function Stealth.hideScript(s)  if s ~= nil then ourScripts[s] = true end return s end

-- ---- hook helpers ---------------------------------------------------------
-- CRITICAL: after hookfunction(real, repl), the `real` OBJECT behaves like repl.
-- So the replacement must NOT call `real` on its passthrough path (that would be
-- infinite recursion -> C stack overflow). We clone the original FIRST and have
-- the replacement call the unhooked clone. If we can't clone, we fall back to a
-- plain global swap (which leaves `real` itself untouched, so calling it is safe).
local function emplace(container, name, build)
	if type(container) ~= "table" then return end
	local real = rawget(container, name)
	if type(real) ~= "function" then return end
	if hookf and clonef then
		local okc, orig = pcall(clonef, real)
		if okc and type(orig) == "function" then
			local repl = newcc(build(orig))         -- repl -> clone (unhooked): safe
			genuineFns[repl] = true; hiddenObjs[repl] = true
			if pcall(hookf, real, repl) then return end
		end
	end
	-- fallback: global/table swap, repl -> real (real is NOT hooked here): safe
	local repl = newcc(build(real))
	genuineFns[repl] = true; hiddenObjs[repl] = true
	pcall(rawset, container, name, repl)
end

local function spoof(name, build)            emplace(realG, name, build) end
local function spoofIn(tbl, name, build)     emplace(tbl, name, build) end

-- filter our hidden/genuine objects out of an array-like result table.
local function filterArray(t)
	if type(t) ~= "table" then return t end
	local out = {}
	for i = 1, #t do
		local v = t[i]
		if not (hiddenObjs[v] or genuineFns[v]) then out[#out + 1] = v end
	end
	return out
end

-- ===========================================================================
function Stealth.install(opts)
	if installed then return end
	installed = true
	opts = opts or {}
	local fakeName = opts.spoofName            -- nil => "no executor"
	local fakeVer  = opts.spoofVersion or "1.0.0"

	-- DISGUISE: a real game LocalScript (cloneref'd) to report as the "calling
	-- script", so introspection sees a legit script instead of getcallingscript()
	-- == nil (which screams "injected"). On by default; opts.disguise=false to skip.
	local decoyScript = nil
	if opts.disguise ~= false then
		pcall(function()
			local lp = game:GetService("Players").LocalPlayer
			local char = lp and lp.Character
			decoyScript = (char and char:FindFirstChild("Animate"))
				or (lp and lp:FindFirstChildWhichIsA("LocalScript", true))
		end)
		if decoyScript then pcall(function() decoyScript = cloneref_(decoyScript) end) end
	end

	-- 1) IDENTITY ----------------------------------------------------------
	for _, n in ipairs({ "identifyexecutor", "getexecutorname", "iexecutor" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end

	-- 2) CLOSURE CHECKS ----------------------------------------------------
	spoof("iscclosure",       function(r) return function(f) if genuineFns[f] then return true  end return r(f) end end)
	spoof("isexecutorclosure",function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("isourclosure",     function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("islclosure",       function(r) return function(f) if genuineFns[f] then return false end return r(f) end end)
	spoof("checkcaller",      function(r) return function() return false end end)
	-- stable fake hash for our funcs so repeated checks stay consistent
	spoof("getfunctionhash",  function(r) return function(f) if genuineFns[f] then return "00000000000000000000000000000000" end return r(f) end end)

	-- 3) ENVIRONMENT / GC scans -- strip our objects ----------------------
	spoof("getgc",     function(r) return function(...) return filterArray(r(...)) end end)
	spoof("filtergc",  function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	spoof("getreg",    function(r) return function(...) return filterArray(r(...)) end end)
	-- getgenv/getrenv must keep identity (callers rely on it); objects already hidden via getgc

	-- 4) INSTANCE scans -- strip our injected instances -------------------
	spoof("getinstances",    function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getnilinstances", function(r) return function(...) return filterArray(r(...)) end end)

	-- 5) SCRIPT scans -- hide our scripts/closures ------------------------
	spoof("getloadedmodules", function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getrunningscripts",function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getscripts",       function(r) return function(...) return filterArray(r(...)) end end)
	spoof("getcallingscript", function(r) return function(...) local s = r(...); if ourScripts[s] or s == nil then return decoyScript end return s end end)
	spoof("getscriptbytecode",function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscriptclosure", function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("getscripthash",    function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	spoof("getsenv",          function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- 6) DEBUG introspection -- blank out for OUR functions ---------------
	if debug then
		spoofIn(debug, "getupvalue",  function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getupvalues", function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getconstant", function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getconstants",function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
		spoofIn(debug, "getproto",    function(r) return function(f, ...) if genuineFns[f] then return nil end return r(f, ...) end end)
		spoofIn(debug, "getprotos",   function(r) return function(f, ...) if genuineFns[f] then return {}  end return r(f, ...) end end)
	end
	-- top-level mirrors (some executors expose these globally too)
	for _, n in ipairs({ "getupvalue","getupvalues","getconstant","getconstants","getproto","getprotos" }) do
		spoof(n, function(r) return function(f, ...)
			if genuineFns[f] then
				if string.sub(n, -1) == "s" then return {} end
				return nil
			end
			return r(f, ...)
		end end)
	end

	-- 7) common executor extras (Volt/Synapse/etc. spellings that may exist) ----
	for _, n in ipairs({ "getexecutorname", "getexecutor", "getexecutorinfo" }) do
		spoof(n, function() return function()
			if fakeName then return fakeName, fakeVer end
			return nil
		end end)
	end
	-- decompiler-style probes: refuse on our scripts
	for _, n in ipairs({ "decompile", "disassemble", "dumpstring" }) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return "" end return r(s, ...) end end)
	end

	-- 7b) Potassium / extended closure + thread + hook checks --------------
	-- the big one: isfunctionhooked must say NO for the funcs your cheat hooks
	spoof("isfunctionhooked", function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isnewcclosure",    function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	spoof("isourclosure",     function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	-- "is this the executor / a hook thread" -> no
	spoof("isourthread",      function(r) return function() return false end end)
	-- thread/script linkage: don't reveal our scripts
	spoof("getscriptfromthread", function(r) return function(t, ...) local s = r(t, ...) if ourScripts[s] then return nil end return s end end)
	spoof("getscriptthread",     function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	spoof("gettenv",             function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)

	-- Potassium oth.* (original-thread hooking) table
	local oth = rawget(realG, "oth")
	if type(oth) == "table" then
		spoofIn(oth, "is_hook_thread", function(r) return function() return false end end)
	end

	-- debug.* extras present on Potassium
	if debug then
		spoofIn(debug, "getcallstack", function(r) return function(...) return r(...) end end)  -- seam: frames aren't our objects
		-- getregistry: return a filtered COPY with our objects removed (AC scans are read-only)
		spoofIn(debug, "getregistry", function(r) return function(...)
			local reg = r(...)
			if type(reg) ~= "table" then return reg end
			local out = {}
			for k, v in pairs(reg) do
				if not (hiddenObjs[k] or hiddenObjs[v] or genuineFns[k] or genuineFns[v]) then
					out[k] = v
				end
			end
			return out
		end end)
		spoofIn(debug, "getinfo", function(r) return function(...) return r(...) end end)  -- seam
	end

	-- metatable seams: only safe to touch CONDITIONALLY. We do NOT blanket-fake
	-- getrawmetatable/getnamecallmethod -- faking the real game metatable breaks
	-- everything. If YOUR cheat hooks __namecall, register the clean function via
	-- Stealth.markGenuine(yourHook) and add a targeted getrawmetatable spoof.

	-- 8) USER-SUPPLIED EXTENSIONS (add Volt-specific names without editing code) -
	--    opts.identity   = { "voltname", ... }     -> spoofed like identifyexecutor
	--    opts.gcFilters  = { "somelist", ... }     -> array results have our objs removed
	--    opts.genuine    = { "iscustom", ... }     -> return clean for our funcs
	--    opts.scriptHide = { "getbytecode2", ... } -> return nothing for our scripts
	for _, n in ipairs(opts.identity or {}) do
		spoof(n, function() return function() if fakeName then return fakeName, fakeVer end return nil end end)
	end
	for _, n in ipairs(opts.gcFilters or {}) do
		spoof(n, function(r) return function(...) local t = r(...) return type(t)=="table" and filterArray(t) or t end end)
	end
	for _, n in ipairs(opts.genuine or {}) do
		spoof(n, function(r) return function(f, ...) if genuineFns[f] then return false end return r(f, ...) end end)
	end
	for _, n in ipairs(opts.scriptHide or {}) do
		spoof(n, function(r) return function(s, ...) if ourScripts[s] then return nil end return r(s, ...) end end)
	end

	return true
end

return Stealth

end)()
local Memory = (function()
--!nonstrict
-- ============================================================================
--  Memory.lua  --  resource scope + leak/overflow protection
--
--  Every thread, connection and disposable the VM creates is registered in a
--  scope. When the script ends (return, error, or tamper) the scope is torn down
--  deterministically: threads cancelled, connections disconnected, tables
--  cleared, GC forced. Plus a budget guard that collects GC the moment memory
--  crosses a threshold, so a runaway/hostile script can't balloon the VM.
--
--  Design notes:
--   * Registries that hold game objects use WEAK keys so they never pin memory.
--   * The scope holds STRONG refs to threads/connections (so it can cancel them)
--     but cleanup is GUARANTEED to run, bounding their lifetime.
--   * Counters are capped; nothing grows unbounded.
-- ============================================================================

local Memory = {}
Memory.__index = Memory

local taskLib   = task
local taskSpawn = (taskLib and taskLib.spawn) or spawn
local taskWait  = (taskLib and taskLib.wait) or wait
local taskDefer = (taskLib and taskLib.defer) or taskSpawn
local taskCancel = taskLib and taskLib.cancel
local cg = collectgarbage

local MAX_TRACKED = 4096   -- hard cap so the bookkeeping itself can't leak

function Memory.new()
	return setmetatable({
		alive = true,
		threads = {},
		conns = {},
		disposers = {},
		count = 0,
	}, Memory)
end

local function bounded(self)
	return self.count < MAX_TRACKED
end

-- spawn a tracked thread (auto-cancelled on cleanup)
function Memory:spawn(fn)
	if not self.alive or not bounded(self) then return end
	local co = taskSpawn(fn)
	self.threads[#self.threads + 1] = co
	self.count = self.count + 1
	return co
end

-- track an arbitrary resource with a disposer
function Memory:track(obj, dispose)
	if not self.alive or not bounded(self) then return obj end
	if dispose then
		self.disposers[#self.disposers + 1] = dispose
		self.count = self.count + 1
	end
	return obj
end

-- track a signal connection (auto-disconnected on cleanup)
function Memory:connect(signal, fn)
	if not self.alive or not bounded(self) then return end
	local ok, c = pcall(function() return signal:Connect(fn) end)
	if ok and c then
		self.conns[#self.conns + 1] = c
		self.count = self.count + 1
		return c
	end
end

-- deterministic teardown -- safe to call multiple times
function Memory:cleanup()
	if not self.alive then return end
	self.alive = false
	for _, c in ipairs(self.conns) do
		pcall(function() if c.Disconnect then c:Disconnect() elseif c.disconnect then c:disconnect() end end)
	end
	if taskCancel then
		for _, co in ipairs(self.threads) do pcall(taskCancel, co) end
	end
	for _, d in ipairs(self.disposers) do pcall(d) end
	self.conns, self.threads, self.disposers, self.count = {}, {}, {}, 0
	if cg then pcall(cg, "collect") end
end

-- memory-budget guard: force GC when usage crosses the threshold; if it stays
-- over after a collect, escalate to onOverflow (the Vm halts).
function Memory:guard(opts)
	opts = opts or {}
	local budgetKB = opts.budgetKB or 700000   -- ~700 MB ceiling by default
	local interval = opts.interval or 4
	self:spawn(function()
		while self.alive do
			taskWait(interval)
			if not self.alive then return end
			local used = cg and cg("count") or 0     -- KB
			if used > budgetKB then
				if cg then pcall(cg, "collect") end
				used = cg and cg("count") or 0
				if used > budgetKB and opts.onOverflow then
					pcall(opts.onOverflow, used)
					return
				end
			end
		end
	end)
end

return Memory

end)()
local Defense = (function()
--!nonstrict
-- ============================================================================
--  Defense.lua  --  detect tools SPYING on your script (anti-tamper)
--
--  These detect OTHER exploiters' inspection tools so your script can react
--  (halt / hide) before its logic or remotes are stolen:
--    * HTTP spy      -- request/http hooked (closure-type check vs captured original)
--    * namecall hook -- __namecall identity changed (IY-style stack inspection)
--    * remote spy    -- gcinfo spike on FireServer (spies deep-clone args)  [opt-in]
--    * Dex explorer  -- weak-table service-cache persistence                [opt-in]
--
--  IMPORTANT: this is ANTI-SPY (protect your code from other exploiters), NOT
--  anti-cheat. It does nothing against the GAME's AC -- and the remote/dex probes
--  even ADD client AC surface (they fire a remote / force GC). Keep those opt-in.
-- ============================================================================

local Defense = {}

local gcinfo_   = gcinfo or function() return (collectgarbage and collectgarbage("count")) or 0 end
local cloneref_ = cloneref or function(x) return x end
local collect   = collectgarbage
local iscc      = iscclosure       -- captured at load; Stealth passes through for non-ours
local dbinfo    = debug and debug.info

-- 1) HTTP spy: a spy hooks the global request -> it becomes an l-closure -------
-- get the real __namecall fn via an errored game:IsA() ----------------------
local function actualNamecall()
	local nc, caller
	if not dbinfo then return nil end
	xpcall(function() return game:IsA() end, function()
		nc, caller = dbinfo(2, "f"), dbinfo(3, "f")
	end)
	return nc, caller
end

local function remoteSpike()
	local ok, spike = pcall(function()
		local re = Instance.new("RemoteEvent")
		local payload = { 1, 2, 3, { nested = true }, "probe" }
		local before = gcinfo_()
		pcall(function() re:FireServer(payload) end)
		local after = gcinfo_()
		pcall(function() re:Destroy() end)
		return after - before
	end)
	return (ok and type(spike) == "number") and spike or 0
end

-- BASELINE: snapshot the environment AFTER your script has set up its own hooks,
-- so YOUR hooks are treated as "normal". Only CHANGES after this (a spy) trigger.
-- Until baseline() is called, the change-detectors stay silent (no false positives).
Defense._snap = nil
function Defense.baseline()
	local realG = (getgenv and getgenv()) or _G
	Defense._snap = {
		ready = true,
		nc = (actualNamecall()),
		request = rawget(realG, "request"),
		http_request = rawget(realG, "http_request"),
		getgc = rawget(realG, "getgc"),     -- a dumper re-hooking getgc -> identity change
		spike = remoteSpike(),
	}
	return true
end

-- getgc-scan: someone re-hooked getgc (a memory scanner/dumper) after baseline
function Defense.detectGetgcHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	local cur = rawget(realG, "getgc")
	if cur and s.getgc and cur ~= s.getgc then return true, "getgc re-hooked (memory scan)" end
	return false
end

-- spy-tool GLOBALS (Hydroxide/SimpleSpy/etc. set flags or tables in getgenv)
local SPY_GLOBALS = { "Hydroxide", "oh_load", "SimpleSpy", "SimpleSpyExecuted", "RemoteSpyV3", "IY_LOADED" }
function Defense.detectSpyGlobals()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		for _, n in ipairs(SPY_GLOBALS) do
			if rawget(g, n) ~= nil then return true, "global " .. n end
		end
	end
	return false
end

-- 1) HTTP spy: the request function IDENTITY changed since baseline (newly hooked)
function Defense.detectHttpSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local realG = (getgenv and getgenv()) or _G
	for _, n in ipairs({ "request", "http_request" }) do
		local cur = rawget(realG, n)
		if cur and s[n] and cur ~= s[n] then return true, n .. " changed after baseline" end
	end
	return false
end

-- 2) namecall hook: __namecall identity changed since baseline
function Defense.detectNamecallHook()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local nc = actualNamecall()
	if s.nc and nc and nc ~= s.nc then return true, "__namecall changed after baseline" end
	return false
end

-- 3) remote spy: gc spike on FireServer rose ABOVE the baseline (a new arg-cloner)
function Defense.detectRemoteSpy()
	local s = Defense._snap
	if not (s and s.ready) then return false end
	local spike = remoteSpike()
	if spike > (s.spike or 0) + 64 then
		return true, "FireServer gc spike " .. tostring(spike)
	end
	return false
end

-- 4a) Infinite Yield (and similar admin tools) set a known global flag --------
function Defense.detectInfiniteYield()
	local ok, g = pcall(getgenv)
	if ok and type(g) == "table" then
		if rawget(g, "IY_LOADED") == true then return true, "Infinite Yield" end
	end
	return false
end

-- 4b) Spy/explorer GUIs (Dex, RemoteSpy, SimpleSpy, Hydroxide, IY window) ------
-- scans CoreGui, the executor-hidden gui (gethui), and PlayerGui by exact name.
-- PRECISE name matching: exact known names, plus controlled version patterns,
-- so we don't false-positive on legit GUIs (e.g. "Dexterity" must NOT match "dex").
local EXACT = {
	["dex"] = true, ["dex explorer"] = true, ["remotespy"] = true, ["remote spy"] = true,
	["simplespy"] = true, ["simple spy"] = true, ["hydroxide"] = true,
}
local function isSpyName(nm)
	if EXACT[nm] then return true end
	if string.match(nm, "^dex%s*v?%d") then return true end          -- "dex v4", "dex 5"
	if string.match(nm, "^remotespy") then return true end
	if string.match(nm, "^simplespy") then return true end
	if string.match(nm, "^hydroxide") then return true end
	return false
end
function Defense.detectSpyGui()
	local parents = {}
	pcall(function() parents[#parents + 1] = game:GetService("CoreGui") end)
	if gethui then pcall(function() parents[#parents + 1] = gethui() end) end
	pcall(function()
		local pg = game:GetService("Players").LocalPlayer:FindFirstChild("PlayerGui")
		if pg then parents[#parents + 1] = pg end
	end)
	for _, p in ipairs(parents) do
		local ok, kids = pcall(function() return p:GetChildren() end)
		if ok then
			for _, c in ipairs(kids) do
				if isSpyName(string.lower(c.Name)) then return true, "GUI: " .. c.Name end
			end
		end
	end
	return false
end

-- 4) Dex: it strong-caches services, so a weak ref survives a forced GC -------
function Defense.detectDex()
	local ok, persisted = pcall(function()
		local weak = setmetatable({}, { __mode = "v" })
		weak[1] = cloneref_(game:GetService("TestService"))
		weak[1] = weak[1]   -- (kept only in the weak table after this scope)
		if collect then for _ = 1, 3 do pcall(collect, "collect") end end
		return weak[1] ~= nil
	end)
	return ok and persisted == true
end

-- SaveInstance guard: hook saveinstance-family so a game/script DUMP is caught
-- the moment it's attempted. Call once (from the watchdog) with the reaction.
function Defense.installSaveGuard(onDetect)
	local realG = (getgenv and getgenv()) or _G
	local newcc_ = newcclosure or function(f) return f end
	local hookf, clonef = hookfunction, clonefunction
	for _, n in ipairs({ "saveinstance", "synsaveinstance", "SaveInstance", "saveplace" }) do
		local f = rawget(realG, n)
		if type(f) == "function" and hookf and clonef then
			local ok, orig = pcall(clonef, f)
			if ok then
				pcall(hookf, f, newcc_(function(...)
					pcall(onDetect, "saveinstance", n)
					return orig(...)
				end))
			end
		end
	end
end

-- run a scan; returns array of { name = , detail = }
function Defense.scan(opts)
	opts = opts or {}
	local found = {}
	local function run(enabled, fn, name, arg)
		if not enabled then return end
		local ok, detail = fn(arg)
		if ok then found[#found + 1] = { name = name, detail = detail or "" } end
	end
	run(opts.iy ~= false,        Defense.detectInfiniteYield, "infinite-yield")
	run(opts.gui ~= false,       Defense.detectSpyGui,        "spy-gui")     -- Dex/RemoteSpy/IY window
	run(opts.globals ~= false,   Defense.detectSpyGlobals,    "spy-global")  -- Hydroxide/SimpleSpy/etc.
	run(opts.http ~= false,      Defense.detectHttpSpy,       "http-spy")
	run(opts.namecall ~= false,  Defense.detectNamecallHook,  "namecall-hook")
	run(opts.getgc ~= false,     Defense.detectGetgcHook,     "getgc-scan")  -- dumper re-hooked getgc
	run(opts.remote == true,     Defense.detectRemoteSpy,     "remote-spy")  -- opt-in (fires a remote)
	run(opts.dex == true,        Defense.detectDex,           "dex")         -- opt-in (forces GC)
	return found
end

-- watchdog: scan promptly then on an interval; call onDetect on first hit.
-- Light probes (IY/GUI/http/namecall) run every tick; HEAVY probes (remote gc
-- spike, Dex weak-table) run only every Nth tick so they don't spam remote-fires
-- or force GC constantly. Heavy probes are ON unless explicitly set to false.
function Defense.watchdog(ctx, onDetect, opts)
	opts = opts or {}
	-- proactive SaveInstance dump guard (fires the moment a dump is attempted)
	pcall(Defense.installSaveGuard, onDetect)
	local body = function()
		local wait_ = (task and task.wait) or wait
		wait_(opts.startDelay or 1)            -- let tools finish loading
		-- reliable signals (IY global, Dex/spy GUI by name, http hook, namecall hook)
		-- react on the FIRST hit. Only the noisy probes need a 2nd confirmation.
		local NOISY = { ["remote-spy"] = true, ["dex"] = true }
		local n, lastHit, confirm = 0, nil, 0
		-- baseline after a grace period so the script's OWN hooks aren't flagged
		-- (Vm also baselines right after the main chunk; whichever fires first wins).
		local graceUntil = (tick and tick() or 0) + (opts.gracePeriod or 4)
		while ctx.alive do
			n = n + 1
			if not (Defense._snap and Defense._snap.ready) and (tick and tick() or 0) >= graceUntil then
				pcall(Defense.baseline)
			end
			local heavy = (n % (opts.heavyEvery or 5)) == 0
			local hits = Defense.scan({
				iy = opts.iy, gui = opts.gui, globals = opts.globals,
				http = opts.http, namecall = opts.namecall, getgc = opts.getgc,
				remote = (opts.remote ~= false) and heavy,   -- throttled, on by default
				dex = (opts.dex ~= false) and heavy,           -- throttled, on by default
				raw = ctx.raw,
			})
			if #hits > 0 then
				local h = hits[1]
				local need = NOISY[h.name] and 2 or 1        -- reliable = instant, noisy = confirm twice
				if h.name == lastHit then confirm = confirm + 1
				else lastHit, confirm = h.name, 1 end
				if confirm >= need then
					pcall(onDetect, h.name, h.detail)
					return
				end
			else
				lastHit, confirm = nil, 0
			end
			wait_(opts.interval or 3)
		end
	end
	if ctx.mem and ctx.mem.spawn then ctx.mem:spawn(body)
	else local s = (task and task.spawn) or spawn if s then s(body) end end
end

return Defense

end)()
local Neuter = (function()
--!nonstrict
-- ============================================================================
--  Neuter.lua  --  best-effort anti-cheat neutralizer (with honest reporting)
--
--  Attempts, in order, every CLIENT-SIDE technique to blind an AC, and REPORTS
--  the outcome of each. If it can't bypass, it says so loudly:
--      "AC bypass fail (error; <reason>)"
--  rather than silently pretending you're undetected.
--
--  Strategies:
--    1. global-spoof   -- replace detection globals with clean-answering versions
--    2. upvalue-patch  -- find ACs that captured detection fns as upvalues and
--                         debug.setupvalue them to our clean versions
--    3. table-patch    -- replace detection fns held in (writable) state tables
--                         (reaches some VM-style ACs)
--    4. report-block   -- best-effort: neutralize the global HTTP request path
--
--  HARD TRUTH (always reported): this is CLIENT-SIDE only. An AC that is
--  VM-obfuscated (functions buried in encrypted state -> nothing to patch) or
--  that validates SERVER-SIDE cannot be bypassed from here. Rivals is both.
-- ============================================================================

local Neuter = {}

local newcc   = newcclosure or function(f) return f end
local getgc_  = getgc
local getups  = getupvalues or (debug and debug.getupvalues)
local setup   = debug and debug.setupvalue
local realG   = (getgenv and getgenv()) or _G
local rawget, rawset = rawget, rawset

local SCAN_CAP = 300000

-- clean-answering replacements: AC sees "no executor, nothing hooked"
local function replacements()
	local R = {}
	R.identifyexecutor   = newcc(function() return nil end)
	R.getexecutorname    = newcc(function() return nil end)
	R.getexecutor        = newcc(function() return nil end)
	R.iscclosure         = newcc(function() return true end)   -- everything looks native
	R.isexecutorclosure  = newcc(function() return false end)
	R.isourclosure       = newcc(function() return false end)
	R.islclosure         = newcc(function() return false end)
	R.isfunctionhooked   = newcc(function() return false end)
	R.checkcaller        = newcc(function() return false end)
	R.isourthread        = newcc(function() return false end)
	return R
end

-- map ORIGINAL function identity -> replacement (for patching captured refs)
local function identityMap(R)
	local m = {}
	for name, repl in pairs(R) do
		local orig = rawget(realG, name)
		if type(orig) == "function" then m[orig] = repl end
	end
	return m
end

-- 1) global spoof -----------------------------------------------------------
function Neuter.globalSpoof(R)
	local n = 0
	for name, repl in pairs(R) do
		if type(rawget(realG, name)) == "function" then
			if hookfunction and clonefunction then
				local ok, orig = pcall(clonefunction, rawget(realG, name))
				if ok then pcall(hookfunction, rawget(realG, name), repl) else pcall(rawset, realG, name, repl) end
			else
				pcall(rawset, realG, name, repl)
			end
			n = n + 1
		end
	end
	return n > 0, "spoofed " .. n .. " globals", 0
end

-- 2) upvalue patch ----------------------------------------------------------
function Neuter.patchUpvalues(idmap)
	if not (getgc_ and getups and setup) then return false, "no getgc/debug.setupvalue" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, fn in ipairs(getgc_(false) or getgc_()) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(fn) == "function" then
				local oku, ups = pcall(getups, fn)
				if oku and type(ups) == "table" then
					for i, uv in pairs(ups) do
						if idmap[uv] then
							if pcall(setup, fn, i, idmap[uv]) then patched = patched + 1 end
						end
					end
				end
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " captured upvalue(s) of " .. scanned .. " closures", patched
end

-- 3) table patch (reaches some VM-style ACs that read fns from state tables) -
function Neuter.patchTables(idmap)
	if not getgc_ then return false, "no getgc" end
	local patched, scanned = 0, 0
	pcall(function()
		for _, t in ipairs(getgc_(true)) do
			if scanned > SCAN_CAP then break end
			scanned = scanned + 1
			if type(t) == "table" then
				pcall(function()
					for k, v in pairs(t) do
						if idmap[v] then
							if pcall(function() t[k] = idmap[v] end) then patched = patched + 1 end
						end
					end
				end)
			end
		end
	end)
	return patched > 0, "patched " .. patched .. " table slot(s)", patched
end

-- 4) report block (best-effort) --------------------------------------------
function Neuter.blockReporting()
	-- We can only neutralize a report path we can see. The global request is
	-- proxied by Secure already; an AC-internal report channel inside a VM is
	-- not generically locatable, so report this honestly.
	return false, "report channel not generically locatable (AC-internal)"
end

-- orchestrate ---------------------------------------------------------------
function Neuter.run(opts)
	opts = opts or {}
	local logf = opts.log or function(m) pcall(warn, m) end
	local R = replacements()
	local idmap = identityMap(R)

	local results, patched = {}, 0
	local function strat(name, fn, ...)
		local ok, detail, n = fn(...)
		results[#results + 1] = { name = name, ok = ok, detail = detail }
		if type(n) == "number" then patched = patched + n end
		logf("[Neuter] " .. name .. ": " .. (ok and "OK" or "FAIL") .. " -- " .. tostring(detail))
	end

	strat("global-spoof",  Neuter.globalSpoof, R)
	strat("upvalue-patch", Neuter.patchUpvalues, idmap)
	strat("table-patch",   Neuter.patchTables, idmap)
	strat("report-block",  Neuter.blockReporting)

	-- VERDICT (honest)
	local verdict
	if patched > 0 then
		verdict = "client checks neutralized (" .. patched .. " refs patched). "
			.. "WARNING: server-side validation is NOT affected -- this is not full immunity."
		logf("[Neuter] result: PARTIAL -- " .. verdict)
	else
		verdict = "no patchable detection refs found -- AC is VM-obfuscated/absent or "
			.. "captures privately; nothing to neutralize client-side."
		logf("AC bypass fail (error; " .. verdict .. ")")
	end

	return { patched = patched, results = results, ok = patched > 0, verdict = verdict }
end

return Neuter

end)()
local License = (function()
--!nonstrict
-- ============================================================================
--  License.lua  --  key / HWID whitelist, expiry, server validation, delivery
--
--  Anti-leak core. A protected script can require a valid KEY (+ optional HWID
--  lock) before it runs, enforce an EXPIRY, and/or fetch its real payload from
--  YOUR server only after the key checks out (so a leaked file is useless).
--
--  Validation order (any you configure):
--    1. expiry      -- refuse if past opts.expiry (server time when possible)
--    2. local keys  -- opts.keys = { "KEY1", ... } embedded allow-list
--    3. server      -- GET opts.endpoint?key=..&hwid=..  -> body must contain "ok"
--  If none configured, it allows (no license).
-- ============================================================================

local License = {}

local function httpGet(url)
	local fns = {
		function() return game:HttpGetAsync(url) end,
		function() return game:HttpGet(url) end,
		function() return request and request({ Url = url, Method = "GET" }).Body end,
	}
	for _, f in ipairs(fns) do
		local ok, body = pcall(f)
		if ok and type(body) == "string" then return body end
	end
	return nil
end

-- stable per-machine id
function License.hwid()
	local id
	pcall(function() id = (gethwid and gethwid()) or (get_hwid and get_hwid()) end)
	if not id then pcall(function() id = game:GetService("RbxAnalyticsService"):GetClientId() end) end
	return tostring(id or "unknown")
end

-- tamper-resistant time: try a web time source, fall back to os.time
function License.now()
	local body = httpGet("https://worldtimeapi.org/api/timezone/Etc/UTC.txt")
	if body then
		local ut = string.match(body, "unixtime:%s*(%d+)")
		if ut then return tonumber(ut) end
	end
	return os.time and os.time() or 0
end

local function inList(list, key)
	for _, k in ipairs(list) do if k == key then return true end end
	return false
end

-- returns ok, reason
function License.validate(opts)
	opts = opts or {}

	if opts.expiry then
		local now = License.now()
		if now and now > 0 and now > opts.expiry then
			return false, "license expired"
		end
	end

	if opts.endpoint then
		local hwid = License.hwid()
		local sep = string.find(opts.endpoint, "?", 1, true) and "&" or "?"
		local url = opts.endpoint .. sep .. "key=" .. tostring(opts.key or "")
			.. "&hwid=" .. hwid
		local body = httpGet(url)
		if not body then return false, "license server unreachable" end
		local lb = string.lower(body)
		if string.find(lb, "ok", 1, true) or string.find(lb, "valid", 1, true) then
			return true, "ok", body  -- body may carry the payload for server-delivery
		end
		return false, "key rejected by server"
	end

	if opts.keys then
		if opts.key and inList(opts.keys, opts.key) then return true, "ok" end
		return false, "invalid key"
	end

	return true, "no license configured"
end

-- SERVER-SIDE DELIVERY: validate, and if the server returns the (encrypted)
-- payload in its response, return it so the loader can run it. Body format the
-- reference server uses:  "ok\n<base64-xored-payload>"  (key is the xor key).
function License.deliver(opts)
	local ok, reason, body = License.validate(opts)
	if not ok then return nil, reason end
	if body then
		local nl = string.find(body, "\n", 1, true)
		if nl then return string.sub(body, nl + 1), "ok" end
	end
	return nil, "validated (no payload in response)"
end

return License

end)()
local Vm = (function()
--!nonstrict
-- ============================================================================
--  Vm.lua  --  main entry of the Vm protection runtime
--
--  Orchestrates Secure (capture+proxies), Environment (sandbox), and Integrity
--  (anti-tamper), then runs the wrapped script inside the sealed runtime.
--
--  API:
--    Vm.run(chunk [, opts])     -- chunk = source string OR a function
--    Vm.protect(fn [, opts])    -- returns a hardened wrapper of fn
--
--  opts = {
--    name     = "Sell a Lemon",      -- label for errors/telemetry
--    strict   = false,                -- abort if executor funcs look pre-hooked
--    interval = 2,                    -- watchdog period (seconds)
--    onTamper = function(reason) end, -- override default self-destruct
--    checksum = "<fnv hash>",         -- optional source integrity pin
--  }
-- ============================================================================

local Crypt       = Crypt
local Secure      = Secure
local Environment = Environment
local Integrity   = Integrity
local Stealth     = Stealth
local Memory      = Memory
local Defense     = Defense
local Neuter      = Neuter
local License     = License

local Vm = {}
Vm._VERSION = "1.0.0"

local realG = (getgenv and getgenv()) or (getfenv and getfenv(0)) or _G
local loadstr = loadstring or load
local setfenv_ = setfenv

-- default self-destruct: wipe the sandbox + raise, so a tampered run cannot
-- continue executing the protected logic.
local function defaultTamper(ctx, reason)
	ctx.alive = false
	-- neuter the proxies so any in-flight call resolves to nothing
	for k in pairs(ctx.proxies) do ctx.proxies[k] = nil end
	if ctx.mem then pcall(function() ctx.mem:cleanup() end) end  -- free threads/conns
	error("[Vm] integrity violation (" .. tostring(reason) .. ") -- halted", 0)
end

-- Build a fresh, sealed runtime context.
local function newContext(opts)
	-- install anti-detection FIRST (as early as we can), then hide our own
	-- objects from gc/closure scans so the spoofing can't be traced back to us.
	if opts.stealth ~= false then
		pcall(Stealth.install, opts.stealthOpts or {})
	end

	-- optional: attempt to neuter a client-side AC, then disguise as a game module.
	-- Reports "AC bypass fail (error; ...)" if it can't (VM-obfuscated / server-side).
	if opts.neuterAC then
		pcall(Neuter.run, type(opts.neuterAC) == "table" and opts.neuterAC or {})
	end

	local raw = Secure.capture()
	local proxies = Secure.proxies(raw)
	local fingerprint = Secure.fingerprint(proxies)
	local env, envMT, _store, envLock = Environment.build(proxies, realG)

	-- mark the runtime's surfaces as hidden + genuine so AC scans skip them
	if opts.stealth ~= false then
		Stealth.hide(raw); Stealth.hide(proxies); Stealth.hide(env)
		for _, fn in pairs(proxies) do
			if type(fn) == "function" then Stealth.markGenuine(fn) end
		end
	end

	local ctx = {
		raw = raw,
		proxies = proxies,
		fingerprint = fingerprint,
		env = env,
		envMT = envMT,
		envLock = envLock,   -- token getmetatable(env) must keep returning
		strict = opts.strict or false,
		interval = opts.interval or 2,
		alive = true,
		name = opts.name or "script",
		mem = Memory.new(),   -- resource scope: tracks every thread/connection
	}

	-- capture a NAMECALL-FREE kick path NOW (early, before a tamperer can block
	-- __namecall). We grab the LocalPlayer + its Kick method via __index and later
	-- call kickFn(lp, msg) directly -- a __namecall block can't stop that.
	pcall(function()
		local plrs = game:GetService("Players")
		ctx.lp = plrs.LocalPlayer
		ctx.kickFn = ctx.lp and ctx.lp.Kick
	end)

	return ctx
end

-- Core: run a function inside a sealed context with integrity enforced.
function Vm.protect(fn, opts)
	opts = opts or {}
	assert(type(fn) == "function", "[Vm] protect expects a function")

	return function(...)
		local ctx = newContext(opts)

		-- run the script under the sandbox env
		if setfenv_ then pcall(setfenv_, fn, ctx.env) end

		local onTamper = function(reason)
			if opts.onTamper then pcall(opts.onTamper, reason) end
			defaultTamper(ctx, reason)
		end

		-- startup integrity gate
		local ok, reason = Integrity.startup(ctx)
		if not ok then return onTamper(reason) end

		-- background watchdog (tracked by the memory scope)
		Integrity.watchdog(ctx, onTamper)

		-- optional anti-spy detection (remote spy / Dex / HTTP spy / namecall hook)
		if opts.antiSpy then
			local o = type(opts.antiSpy) == "table" and opts.antiSpy or {}
			Defense.watchdog(ctx, function(name, detail)
				if opts.onSpy then pcall(opts.onSpy, name, detail) end
				-- clean message (no details). Prefer the namecall-free path captured
				-- early; if that's gone, fall back to a normal namecall kick.
				if o.kick ~= false then
					local kicked = false
					if ctx.kickFn and ctx.lp then
						kicked = pcall(ctx.kickFn, ctx.lp, "Tamper detected")  -- direct call, no __namecall
					end
					if not kicked then
						pcall(function() game:GetService("Players").LocalPlayer:Kick("Tamper detected") end)
					end
				end
				-- crash the tamperer's client -- the guaranteed fallback if the kick is
				-- blocked. IMPORTANT: NOT wrapped in pcall (a pcall would swallow the
				-- out-of-memory error and stop the crash). Allocations are kept alive in
				-- `sink` so GC can't reclaim them; big chunks per iteration -> OOM in ~1s.
				-- Runs in its own thread so cleanup can't cancel it.
				if o.crash ~= false then
					local sp = (task and task.spawn) or spawn
					local wait_ = (task and task.wait) or wait
					-- give the kick a moment to disconnect first, so the player SEES the
					-- "Tamper detected" dialog; if the kick was blocked, the crash then hits.
					pcall(function() wait_(o.crashDelay or 1.5) end)
					local crasher = function()
						local sink = {}
						while true do
							if table.create then
								sink[#sink + 1] = table.create(16777216, 0)   -- ~256MB/iter
							else
								sink[#sink + 1] = string.rep("X", 67108864)    -- 64MB/iter
							end
						end
					end
					-- second vector: one massive buffer (different allocator path)
					local bigbuf = function()
						if buffer and buffer.create then local _ = buffer.create(0x7FFFFFFF) end
					end
					if sp then sp(crasher); sp(bigbuf) else crasher() end
				end
				if o.halt ~= false then
					ctx.alive = false
					pcall(function() ctx.mem:cleanup() end)
				end
			end, o)
		end

		-- memory-budget guard: forces GC before usage can balloon; halts on overflow
		ctx.mem:guard({
			budgetKB = opts.memBudgetKB,
			interval = opts.interval,
			onOverflow = function(used)
				ctx.alive = false
				if opts.onOverflow then pcall(opts.onOverflow, used) end
				pcall(function() ctx.mem:cleanup() end)
			end,
		})

		-- execute the script's main chunk
		local results = { pcall(fn, ...) }

		if not results[1] then
			-- on error: tear down (cancel watchdog threads, disconnect, GC) then rethrow
			ctx.alive = false
			pcall(function() ctx.mem:cleanup() end)
			error("[Vm:" .. ctx.name .. "] " .. tostring(results[2]), 0)
		end

		-- SUCCESS: do NOT tear down. Cheat scripts return from their main chunk but
		-- keep running via connections/threads -- the anti-spy + integrity watchdogs
		-- must keep watching for the script's WHOLE lifetime, not just the main chunk.
		-- (Teardown happens on tamper, overflow, or spy-kick.)

		-- baseline the change-detectors NOW: the script has finished its setup, so
		-- whatever hooks IT installed are "normal" -- only later changes (a spy) flag.
		if opts.antiSpy then pcall(Defense.baseline) end

		return table.unpack(results, 2)
	end
end

-- Convenience: load a source string and protect+run it.
function Vm.run(chunk, opts)
	opts = opts or {}

	-- LICENSE gate (key / HWID / expiry / server). Runs before anything executes.
	if opts.license then
		local ok, reason = License.validate(opts.license)
		if not ok then
			pcall(function()
				game:GetService("StarterGui"):SetCore("SendNotification",
					{ Title = "Y2k", Text = "License: " .. tostring(reason), Duration = 6 })
			end)
			error("[Vm] license check failed: " .. tostring(reason), 0)
		end
	end

	-- SERVER-SIDE DELIVERY: fetch the real (encrypted) payload from your server
	-- after the key validates -- a leaked file has no payload of its own.
	if opts.deliver then
		local payload, reason = License.deliver(opts.deliver)
		if not payload then error("[Vm] delivery failed: " .. tostring(reason), 0) end
		chunk = (opts.deliver.key and Crypt.open(payload, opts.deliver.key)) or payload
	end

	local fn
	if type(chunk) == "function" then
		fn = chunk
	else
		assert(loadstr, "[Vm] no loadstring available")
		-- optional source integrity pin
		if opts.checksum and Crypt.hash(chunk) ~= opts.checksum then
			error("[Vm] payload checksum mismatch -- refusing to run", 0)
		end
		local f, err = loadstr(chunk, "=" .. (opts.name or "Vm"))
		if not f then error("[Vm] load error: " .. tostring(err), 0) end
		fn = f
	end
	return Vm.protect(fn, opts)()
end

return Vm

end)()

local __k = 'gQvYXQfKO5SMuFwN9ux6Bg0A'
local __p = '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'
local __src = Crypt.open(__p, __k)
-- watermark: Y2k-jyvZrSSV2fbD
return Vm.run(__src, { name = 'Dandy World/Dandy-World', checksum = 3492352745, interval = 2, watermark = 'Y2k-jyvZrSSV2fbD', neuterAC = true, antiSpy = { kick = true, halt = true }, license = { key = (getgenv and (getgenv().SCRIPT_KEY or getgenv().Key)) or _G.Key, endpoint = 'https://y2k-keys.y2kscript.workers.dev/check' } })
